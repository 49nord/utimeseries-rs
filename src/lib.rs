extern crate byte_conv;
extern crate cast;
#[macro_use]
extern crate quick_error;

use byte_conv::As;
use std::{io, mem, time, u32};
use std::marker::PhantomData;
use std::io::{Read, Seek, SeekFrom, Write};

pub mod database;
mod err;
#[macro_use]
mod util;

pub use err::Error;
use util::{ReadRaw, Tell};

const MAGIC_NUMBER: u32 = 0x01755453;
const FILE_HEADER_SIZE: u64 = mem::size_of::<FileHeader>() as u64;
const BLOCK_HEADER_SIZE: u64 = mem::size_of::<BlockHeader>() as u64;

#[derive(Copy, Clone, Debug)]
#[repr(C)]
struct FileHeader {
    /// Magic number, used for sanity checks
    magic_number: u32,

    // Number of items in a single block
    block_length: u32,

    // Interval inside blocks
    interval_ns: u64,

    // Initial time value
    start_delta_s: u64,
    start_delta_ns: u32,
}

impl FileHeader {
    fn new(
        block_length: u32,
        start: time::SystemTime,
        interval: time::Duration,
    ) -> Result<Self, Error> {
        let epoch_delta = start
            .duration_since(time::UNIX_EPOCH)
            .map_err(|_| Error::TimeOutOfRange)?;

        Ok(FileHeader {
            magic_number: MAGIC_NUMBER,
            block_length,
            start_delta_s: epoch_delta.as_secs(),
            start_delta_ns: epoch_delta.subsec_nanos(),
            interval_ns: util::duration_ns64(interval).ok_or_else(|| Error::IntervalOutOfRange)?,
        })
    }

    #[inline]
    fn load<R: Read>(r: &mut R) -> Result<Self, Error> {
        // read header from file
        let header: FileHeader = unsafe { r.read_raw() }?;

        // verify it is a valid header by checking the magic number
        if header.magic_number != MAGIC_NUMBER {
            Err(Error::CorruptHeader)
        } else {
            Ok(header)
        }
    }

    #[inline]
    fn interval(&self) -> time::Duration {
        util::ns64_duration(self.interval_ns)
    }

    #[inline]
    fn start_time(&self) -> time::SystemTime {
        time::UNIX_EPOCH + time::Duration::new(self.start_delta_s, self.start_delta_ns)
    }

    #[inline]
    fn block_size<T: Sized>(&self) -> u64 {
        BLOCK_HEADER_SIZE + mem::size_of::<T>() as u64 * self.block_length as u64
    }

    #[inline]
    fn nth_block_start<T: Sized>(&self, n: u64) -> u64 {
        FILE_HEADER_SIZE + n * self.block_size::<T>()
    }

    #[inline]
    fn total_blocks<T: Sized>(&self, sz: u64) -> u64 {
        let data_len = sz - FILE_HEADER_SIZE;
        data_len / self.block_size::<T>()
    }
}

#[test]
fn file_header_loads_correctly() {
    let mut buf = Vec::new();

    let header = FileHeader {
        magic_number: MAGIC_NUMBER,
        block_length: 99,
        interval_ns: 987_654_321,
        start_delta_s: 1,
        start_delta_ns: 123_456_789,
    };

    // we're not checking what was written here, most of it is covered by the
    // `read_raw` tests
    buf.write_all(header.as_bytes()).unwrap();

    assert_eq!(mem::size_of::<FileHeader>(), buf.len());

    // loading should work now (magic number matches)
    let restored = FileHeader::load(&mut buf.as_slice()).unwrap();

    assert_eq!(restored.magic_number, MAGIC_NUMBER);
    assert_eq!(restored.block_length, 99);
    assert_eq!(restored.interval_ns, 987_654_321);
    assert_eq!(restored.start_delta_s, 1);
    assert_eq!(restored.start_delta_ns, 123_456_789);
}

#[test]
fn file_header_rejects_too_short() {
    let buf = vec![0x00, 0x12, 0x34, 0x45];

    match FileHeader::load(&mut buf.as_slice()) {
        Err(Error::Io(ref e)) if e.kind() == io::ErrorKind::UnexpectedEof => (),
        otherwise @ _ => {
            panic!("Expected corrupted header error, {:?} instead", otherwise);
        }
    }
}

#[test]
fn file_header_rejects_invalid_magic_number() {
    let buf = vec![
        0x00, 0x12, 0x34, 0x45, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
        0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
        0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    ];

    match FileHeader::load(&mut buf.as_slice()) {
        Err(Error::CorruptHeader) => (),
        otherwise @ _ => {
            panic!("Expected corrupted header error, {:?} instead", otherwise);
        }
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(C)]
struct BlockHeader {
    offset_ns: u64,
}

impl BlockHeader {
    #[inline]
    fn new(offset: time::Duration) -> Result<BlockHeader, Error> {
        Ok(BlockHeader {
            offset_ns: util::duration_ns64(offset).ok_or_else(|| Error::IntervalOutOfRange)?,
        })
    }

    #[inline]
    fn load<R: Read>(r: &mut R) -> Result<Self, Error> {
        Ok(unsafe { r.read_raw() }?)
    }

    #[inline]
    fn duration(&self) -> std::time::Duration {
        util::ns64_duration(self.offset_ns)
    }
}

/// Wraps a writer and writes blocks to it.
#[derive(Debug)]
pub struct TimeseriesWriter<T, W> {
    out: W,
    header: FileHeader,
    _pd: PhantomData<T>,
}

impl<T: Sized, W> TimeseriesWriter<T, W> {
    #[inline]
    fn block_length(&self) -> u32 {
        self.header.block_length
    }
}

impl<T: Sized + Copy, W: Write> TimeseriesWriter<T, W> {
    /// Creates a new `TimeseriesWriter` and writes the file header.
    ///
    /// Each block contains a header with a timestamp, and `block_length` records of type `T`.
    #[inline]
    pub fn create(
        mut out: W,
        block_length: u32,
        start: time::SystemTime,
        interval: time::Duration,
    ) -> Result<Self, Error> {
        // write out header
        let header = FileHeader::new(block_length, start, interval)?;
        out.write_all(header.as_bytes())?;

        Ok(TimeseriesWriter {
            out,
            header,
            _pd: PhantomData::<T>,
        })
    }

    /// Creates a new `TimeseriesWriter` and writes the file header.
    ///
    /// Each block contains a header with a timestamp, and `block_length` records of type `T`. The
    /// interval is given in nanoseconds.
    #[inline]
    pub fn create_with_ns(
        out: W,
        block_length: u32,
        start: time::SystemTime,
        interval_ns: u64,
    ) -> Result<Self, Error> {
        let interval = util::ns64_duration(interval_ns);
        Self::create(out, block_length, start, interval)
    }

    /// Writes a new block; `values` must have exactly `block_length` entries.
    #[inline]
    pub fn record_values(&mut self, offset: time::Duration, values: &[T]) -> Result<(), Error> {
        // check values are of correct size
        if self.block_length() as usize != values.len() {
            return Err(Error::BlockSizeMismatch(
                self.block_length(),
                values.len() as u32,
            ));
        }

        // create a new block header to insert
        let header = BlockHeader::new(offset)?;

        self.out.write_all(header.as_bytes())?;

        // write out all values sequentially
        for val in values {
            self.out.write_all(val.as_bytes())?;
        }

        // no flushing, this is up to the client

        Ok(())
    }

    /// Gets a reference to the underlying writer.
    #[inline]
    pub fn get_ref(&self) -> &W {
        &self.out
    }

    /// Gets a mutable reference to the underlying writer.
    #[inline]
    pub fn get_mut(&mut self) -> &mut W {
        &mut self.out
    }

    /// The start time of the time series.
    #[inline]
    pub fn start_time(&self) -> time::SystemTime {
        self.header.start_time()
    }

    /// The interval of the time series.
    #[inline]
    pub fn interval(&self) -> time::Duration {
        self.header.interval()
    }
}

impl<T: Sized + Copy, W: Write + Seek + Read> TimeseriesWriter<T, W> {
    /// Creates a new `TimeseriesWriter` that appends to the given writer.
    ///
    /// It reads the header from the beginning and then skips to the position after the last
    /// complete block. Additional blocks will be appended from there.
    #[inline]
    pub fn append(mut out: W) -> Result<Self, Error> {
        // get current size by seeking to the end and getting the current pos
        let sz = out.seek(io::SeekFrom::End(0))?;

        // read the header, this will return an error if the header is corrupt
        out.seek(io::SeekFrom::Start(0))?;
        let header = FileHeader::load(&mut out)?;

        // otherwise, seek to insert position, which is after the last
        // correctly written input block
        out.seek(io::SeekFrom::Start(
            header.nth_block_start::<T>(header.total_blocks::<T>(sz)),
        ))?;

        Ok(TimeseriesWriter {
            out,
            header,
            _pd: PhantomData::<T>,
        })
    }

    /// Updates the timeseries' start time, without changing any deltas. Returns the previous start
    /// time.
    ///
    /// **WARNING** The underlying file must be opened in _write_ mode. If it is in append mode, it
    /// will append garbage data to the end of the stream!
    pub fn set_start_time(&mut self, start: time::SystemTime) -> Result<time::SystemTime, Error> {
        let old_start = self.header.start_time();
        self.header = FileHeader::new(self.block_length(), start, self.interval())?;

        // get current position, write header, restore position
        let cur_pos = self.out.tell()?;
        self.out.seek(io::SeekFrom::Start(0))?;
        self.out.write_all(self.header.as_bytes())?;
        self.out.seek(io::SeekFrom::Start(cur_pos))?;

        Ok(old_start)
    }
}

/// Wraps a reader and reads blocks from it.
pub struct TimeseriesReader<T, R> {
    stream: R,
    header: FileHeader,
    _pd: PhantomData<T>,
    stream_length: u64,
}

impl<T: Sized + Copy, R: Read + Seek> TimeseriesReader<T, R> {
    /// Creates a new `TimeseriesReader` with the parameters read from the header at the beginning
    /// of `stream`.
    #[inline]
    pub fn open(mut stream: R) -> Result<Self, Error> {
        stream.seek(SeekFrom::Start(0))?;

        // read header first, stop at first item
        let header = FileHeader::load(&mut stream)?;

        let mut rd = TimeseriesReader {
            stream,
            header,
            _pd: PhantomData,
            stream_length: 0,
        };

        rd.refresh()?;

        Ok(rd)
    }

    /// Checks if the underlying reader has new blocks and makes them available for reading.
    #[inline]
    pub fn refresh(&mut self) -> Result<(), io::Error> {
        let cur_pos = self.stream.tell()?;

        self.stream_length = self.stream.seek(SeekFrom::End(0))?;

        self.stream.seek(SeekFrom::Start(cur_pos))?;

        Ok(())
    }

    #[inline]
    fn block_size(&self) -> u64 {
        self.header.block_size::<T>()
    }

    /// The start time of the time series, as read from the file header.
    #[inline]
    pub fn start_time(&self) -> time::SystemTime {
        self.header.start_time()
    }

    /// The interval of the time series, as read from the file header.
    #[inline]
    pub fn interval(&self) -> time::Duration {
        self.header.interval()
    }

    #[inline]
    fn block_length(&self) -> u32 {
        self.header.block_length
    }

    #[inline]
    fn file_pos(&mut self) -> io::Result<u64> {
        self.stream.tell()
    }

    #[inline]
    fn load_block_header(&mut self) -> Result<BlockHeader, Error> {
        Ok(BlockHeader::load(&mut self.stream)?)
    }

    #[inline]
    fn load_record(&mut self) -> Result<T, Error> {
        Ok(unsafe { self.stream.read_raw() }?)
    }

    /// Returns a new `TimestampIterator`, with the timestamps of all blocks starting from the
    /// current position of the reader.
    #[inline]
    pub fn into_timestamp_iterator(self) -> TimestampIterator<T, R> {
        TimestampIterator { reader: self }
    }

    /// Returns a new `BlockIterator`, with the all blocks starting from the current position of the
    /// reader.
    #[inline]
    pub fn into_block_iterator(self) -> BlockIterator<T, R> {
        BlockIterator { reader: self }
    }

    /// Returns a new `RecordIterator`, that goes through all records starting from the current
    /// position of the reader.
    #[inline]
    pub fn into_record_iterator(self) -> RecordIterator<T, R> {
        RecordIterator::new(BlockIterator { reader: self })
    }
}

/// An iterator over all timestamps of the blocks in a time series.
pub struct TimestampIterator<T, R> {
    reader: TimeseriesReader<T, R>,
}

impl<T: Sized + Copy, R: Read + Seek> TimestampIterator<T, R> {
    /// Returns the underlying `TimeseriesReader`.
    #[inline]
    pub fn into_inner(self) -> TimeseriesReader<T, R> {
        self.reader
    }

    /// Refreshes the underlying `TimeseriesReader`, so that new blocks become available.
    #[inline]
    pub fn refresh(&mut self) -> Result<(), io::Error> {
        self.reader.refresh()
    }
}

impl<T, R> Iterator for TimestampIterator<T, R>
where
    T: Copy + Sized,
    R: Read + Seek,
{
    type Item = Result<time::Duration, Error>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // initial position
        let pos = iter_try!(self.reader.file_pos());

        // if there's not enough space for another block, don't read
        if pos + self.reader.block_size() > self.reader.stream_length {
            return None;
        }

        // at this point we can be sure that we have enough "runway" to read
        // the next block
        let block_header = iter_try!(self.reader.load_block_header());

        // Skip the block's data.
        let records_size = (self.reader.block_size() - BLOCK_HEADER_SIZE) as i64;
        iter_try!(self.reader.stream.seek(SeekFrom::Current(records_size)));

        Some(Ok(block_header.duration()))
    }
}

/// An iterator over all blocks in a time series.
pub struct BlockIterator<T, R> {
    reader: TimeseriesReader<T, R>,
}

impl<T: Sized + Copy, R: Read + Seek> BlockIterator<T, R> {
    /// Returns the underlying `TimeseriesReader`.
    #[inline]
    pub fn into_inner(self) -> TimeseriesReader<T, R> {
        self.reader
    }

    /// Refreshes the underlying `TimeseriesReader`, so that new blocks become available.
    #[inline]
    pub fn refresh(&mut self) -> Result<(), io::Error> {
        self.reader.refresh()
    }
}

impl<T, R> Iterator for BlockIterator<T, R>
where
    T: Copy + Sized,
    R: Read + Seek,
{
    type Item = Result<(time::Duration, Vec<T>), Error>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // initial position
        let pos = iter_try!(self.reader.file_pos());
        if pos + self.reader.block_size() > self.reader.stream_length {
            return None;
        }
        let block_header = iter_try!(self.reader.load_block_header());

        // load data
        let n = self.reader.block_length() as usize;
        let mut buf = Vec::with_capacity(n);
        for _ in 0..n {
            buf.push(iter_try!(self.reader.load_record()))
        }

        Some(Ok((block_header.duration(), buf)))
    }
}

/// An iterator over all records in a time series.
///
/// It returns every block's records in sequence, together with the corresponding time offset.
pub struct RecordIterator<T, R> {
    block_iter: BlockIterator<T, R>,
    offset: time::Duration,
    data: Vec<T>,
    index: usize,
}

impl<T: Sized + Copy, R: Read + Seek> RecordIterator<T, R> {
    #[inline]
    fn new(block_iter: BlockIterator<T, R>) -> RecordIterator<T, R> {
        RecordIterator {
            block_iter,
            offset: time::Duration::from_millis(0),
            data: Vec::new(),
            index: 0,
        }
    }

    /// Returns the underlying `TimeseriesReader`.
    #[inline]
    pub fn into_inner(self) -> TimeseriesReader<T, R> {
        self.block_iter.into_inner()
    }

    /// Refreshes the underlying `TimeseriesReader`, so that new blocks become available.
    #[inline]
    pub fn refresh(&mut self) -> Result<(), io::Error> {
        self.block_iter.refresh()
    }
}

impl<T, R> Iterator for RecordIterator<T, R>
where
    T: Copy + Sized,
    R: Read + Seek,
{
    type Item = Result<(time::Duration, T), Error>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // refill current block if empty
        if self.index >= self.data.len() {
            match self.block_iter.next() {
                Some(Ok((offset, data))) => {
                    self.offset = offset;
                    self.data = data;
                    self.index = 0;
                }
                Some(Err(e)) => return Some(Err(e)),
                None => {
                    // no more blocks -> we're done
                    return None;
                }
            }
        }

        // we are guaranteed at least one item now
        let rv = (self.offset, self.data[self.index]);
        self.index += 1;
        self.offset += self.block_iter.reader.interval();

        Some(Ok(rv))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::cmp;
    use std::rc::Rc;
    use std::io::{self, ErrorKind, Read, SeekFrom, Write};
    use std::time::{Duration, SystemTime};

    /// In-memory test data that can be cloned to simulate a file that is simultaneously written to
    /// and read from.
    #[derive(Clone, Default)]
    struct TestFile {
        pos: u64,
        bytes: Rc<RefCell<Vec<u8>>>,
    }

    // Adapted from the `std::io::Cursor` implementation.
    impl Read for TestFile {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let amt = cmp::min(self.pos, self.bytes.borrow().len() as u64) as usize;
            let n = Read::read(&mut &self.bytes.borrow_mut()[amt..], buf)?;
            self.pos += n as u64;
            Ok(n)
        }

        fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
            let amt = cmp::min(self.pos, self.bytes.borrow().len() as u64) as usize;
            Read::read_exact(&mut &self.bytes.borrow_mut()[amt..], buf)?;
            self.pos += buf.len() as u64;
            Ok(())
        }
    }

    // Adapted from the `std::io::Cursor` implementation.
    impl Write for TestFile {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            let pos = self.pos as usize;
            let mut vec = self.bytes.borrow_mut();
            if vec.len() < pos + buf.len() {
                vec.resize(pos + buf.len(), 0);
            }
            vec[pos..pos + buf.len()].copy_from_slice(buf);
            self.pos += buf.len() as u64;
            Ok(buf.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    // Adapted from the `std::io::Cursor` implementation.
    impl Seek for TestFile {
        fn seek(&mut self, style: SeekFrom) -> io::Result<u64> {
            let (base_pos, offset) = match style {
                SeekFrom::Start(n) => {
                    self.pos = n;
                    return Ok(n);
                }
                SeekFrom::End(n) => (self.bytes.borrow().len() as u64, n),
                SeekFrom::Current(n) => (self.pos, n),
            };
            let new_pos = if offset >= 0 {
                base_pos.checked_add(offset as u64)
            } else {
                base_pos.checked_sub((offset.wrapping_neg()) as u64)
            };
            match new_pos {
                Some(n) => {
                    self.pos = n;
                    Ok(self.pos)
                }
                None => Err(io::Error::new(
                    ErrorKind::InvalidInput,
                    "invalid seek to a negative or overflowing position",
                )),
            }
        }
    }

    #[test]
    fn read_and_write() {
        let file = TestFile::default();
        let ms = Duration::from_millis;
        let block1 = vec![1u32, 2u32, 3u32];
        let block2 = vec![4u32, 5u32, 6u32];

        let mut writer = TimeseriesWriter::create(file.clone(), 3, SystemTime::now(), ms(100))
            .expect("create writer");
        writer.record_values(ms(100), &block1).expect("write");
        let mut reader = TimeseriesReader::open(file.clone()).expect("open");
        let mut timestamp_iter = TimeseriesReader::<u32, _>::open(file.clone())
            .expect("open")
            .into_timestamp_iterator();
        let mut block_iter = TimeseriesReader::<u32, _>::open(file.clone())
            .expect("open")
            .into_block_iterator();
        let mut record_iter = TimeseriesReader::<u32, _>::open(file.clone())
            .expect("open")
            .into_record_iterator();

        assert_eq!(3, reader.block_length());
        let header = reader.load_block_header().expect("load header");
        assert_eq!(ms(100), header.duration());
        assert_eq!(1u32, reader.load_record().expect("load record"));
        assert_eq!(2u32, reader.load_record().expect("load record"));
        assert_eq!(3u32, reader.load_record().expect("load record"));
        assert!(reader.load_record().is_err());
        assert_eq!(
            ms(100),
            timestamp_iter.next().expect("ts iter").expect("ts result")
        );
        assert!(timestamp_iter.next().is_none());
        assert_eq!(
            (ms(100), block1.clone()),
            block_iter.next().expect("b iter").expect("b result")
        );
        assert!(block_iter.next().is_none());

        writer.record_values(ms(400), &block2).expect("write");
        let header = reader.load_block_header().expect("load header");
        assert_eq!(ms(400), header.duration());
        assert_eq!(4u32, reader.load_record().expect("load record"));
        assert_eq!(5u32, reader.load_record().expect("load record"));
        assert_eq!(6u32, reader.load_record().expect("load record"));
        assert!(reader.load_record().is_err());
        assert!(timestamp_iter.next().is_none());
        assert!(block_iter.next().is_none());
        assert!(timestamp_iter.refresh().is_ok());
        assert!(block_iter.refresh().is_ok());
        assert!(record_iter.refresh().is_ok());
        assert_eq!(
            ms(400),
            timestamp_iter.next().expect("ts iter").expect("ts result")
        );
        assert!(timestamp_iter.next().is_none());
        assert_eq!(
            (ms(400), block2.clone()),
            block_iter.next().expect("b iter").expect("b result")
        );
        assert!(block_iter.next().is_none());
        assert_eq!(
            vec![
                (ms(100), 1),
                (ms(200), 2),
                (ms(300), 3),
                (ms(400), 4),
                (ms(500), 5),
                (ms(600), 6),
            ],
            record_iter
                .map(|result| result.expect("r iter"))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn into() {
        let file = TestFile::default();
        let ms = Duration::from_millis;
        let block1 = vec![1u32, 2u32, 3u32];
        let block2 = vec![4u32, 5u32, 6u32];
        let block3 = vec![7u32, 8u32, 9u32];

        let mut writer = TimeseriesWriter::create(file.clone(), 3, SystemTime::now(), ms(33))
            .expect("create writer");
        writer.record_values(ms(0), &block1).expect("write");
        writer.record_values(ms(100), &block2).expect("write");
        writer.record_values(ms(200), &block3).expect("write");

        let reader = TimeseriesReader::open(file.clone()).expect("open");
        let mut timestamp_iter = reader.into_timestamp_iterator();

        assert_eq!(
            ms(0),
            timestamp_iter.next().expect("ts iter").expect("ts result")
        );
        let mut block_iter = timestamp_iter.into_inner().into_block_iterator();
        assert_eq!(
            (ms(100), block2.clone()),
            block_iter.next().expect("b iter").expect("b result")
        );
        let record_iter = block_iter.into_inner().into_record_iterator();
        assert_eq!(
            vec![(ms(200), 7), (ms(233), 8), (ms(266), 9)],
            record_iter
                .map(|result| result.expect("r iter"))
                .collect::<Vec<_>>()
        );
    }
}
