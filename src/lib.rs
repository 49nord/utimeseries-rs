extern crate byte_conv;
extern crate cast;
#[macro_use]
extern crate quick_error;

use byte_conv::As;
use std::{io, mem, time, u32};
use std::marker::PhantomData;
use std::io::{Read, Seek, SeekFrom, Write};

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

    fn interval(&self) -> time::Duration {
        util::ns64_duration(self.interval_ns)
    }

    fn start_time(&self) -> time::SystemTime {
        time::UNIX_EPOCH + time::Duration::new(self.start_delta_s, self.start_delta_ns)
    }

    fn block_size<T: Sized>(&self) -> u64 {
        BLOCK_HEADER_SIZE + mem::size_of::<T>() as u64 * self.block_length as u64
    }

    fn nth_block_start<T: Sized>(&self, n: u64) -> u64 {
        FILE_HEADER_SIZE + n * self.block_size::<T>()
    }

    fn total_blocks<T: Sized>(&self, sz: u64) -> u64 {
        let data_len = sz - FILE_HEADER_SIZE;
        data_len - (data_len % self.block_size::<T>())
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
    fn new(offset: time::Duration) -> Result<BlockHeader, Error> {
        Ok(BlockHeader {
            offset_ns: util::duration_ns64(offset).ok_or_else(|| Error::IntervalOutOfRange)?,
        })
    }

    fn load<R: Read>(r: &mut R) -> Result<Self, Error> {
        Ok(unsafe { r.read_raw() }?)
    }

    fn duration(&self) -> std::time::Duration {
        util::ns64_duration(self.offset_ns)
    }
}

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
    pub fn get_ref(&self) -> &W {
        &self.out
    }

    /// Gets a mutable reference to the underlying writer.
    pub fn get_mut(&mut self) -> &mut W {
        &mut self.out
    }
}

impl<T: Sized + Copy, W: Write + Seek + Read> TimeseriesWriter<T, W> {
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
            header: header,
            _pd: PhantomData::<T>,
        })
    }
}

pub struct TimeseriesReader<T, R> {
    stream: R,
    header: FileHeader,
    _pd: PhantomData<T>,
    stream_length: u64,
}

impl<T: Sized + Copy, R: Read + Seek> TimeseriesReader<T, R> {
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

    pub fn refresh(&mut self) -> Result<(), io::Error> {
        let cur_pos = self.stream.tell()?;

        self.stream_length = self.stream.seek(SeekFrom::End(0))?;

        self.stream.seek(SeekFrom::Start(cur_pos))?;

        Ok(())
    }

    fn block_size(&self) -> u64 {
        self.header.block_size::<T>()
    }

    pub fn start_time(&self) -> time::SystemTime {
        self.header.start_time()
    }

    pub fn interval(&self) -> time::Duration {
        self.header.interval()
    }

    #[inline]
    fn block_length(&self) -> u32 {
        self.header.block_length
    }

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

    pub fn into_timestamp_iterator(self) -> TimestampIterator<T, R> {
        TimestampIterator { reader: self }
    }

    pub fn into_block_iterator(self) -> BlockIterator<T, R> {
        BlockIterator { reader: self }
    }

    pub fn into_record_iterator(self) -> RecordIterator<T, R> {
        RecordIterator::new(BlockIterator { reader: self })
    }
}

pub struct TimestampIterator<T, R> {
    reader: TimeseriesReader<T, R>,
}

impl<T: Sized + Copy, R: Read + Seek> TimestampIterator<T, R> {
    pub fn into_inner(self) -> TimeseriesReader<T, R> {
        self.reader
    }

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

pub struct BlockIterator<T, R> {
    reader: TimeseriesReader<T, R>,
}

impl<T: Sized + Copy, R: Read + Seek> BlockIterator<T, R> {
    pub fn into_inner(self) -> TimeseriesReader<T, R> {
        self.reader
    }

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

pub struct RecordIterator<T, R> {
    block_iter: BlockIterator<T, R>,
    offset: time::Duration,
    data: Vec<T>,
    index: usize,
}

impl<T: Sized + Copy, R: Read + Seek> RecordIterator<T, R> {
    pub fn new(block_iter: BlockIterator<T, R>) -> RecordIterator<T, R> {
        RecordIterator {
            block_iter,
            offset: time::Duration::from_millis(0),
            data: Vec::new(),
            index: 0,
        }
    }

    pub fn into_inner(self) -> TimeseriesReader<T, R> {
        self.block_iter.into_inner()
    }

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

    fn next(&mut self) -> Option<Self::Item> {
        // refill current block if empty
        if self.index >= self.data.len() {
            match self.block_iter.next() {
                Some(Ok((offset, data))) => {
                    self.offset = offset;
                    self.data = data;
                    self.index = 0;
                }
                Some(Err(e)) => return Some(Err(e.into())),
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

        return Some(Ok(rv));
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

    #[derive(Clone, Default)]
    struct TestFile {
        pos: u64,
        bytes: Rc<RefCell<Vec<u8>>>,
    }

    // Adapted from the `Cursor` implementation.
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

    // Adapted from the `Cursor` implementation.
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

    // Adapted from the `Cursor` implementation.
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
        writer.record_values(ms(200), &block1).expect("write");
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
        assert_eq!(ms(200), header.duration());
        assert_eq!(1u32, reader.load_record().expect("load record"));
        assert_eq!(2u32, reader.load_record().expect("load record"));
        assert_eq!(3u32, reader.load_record().expect("load record"));
        assert!(reader.load_record().is_err());
        assert_eq!(
            ms(200),
            timestamp_iter.next().expect("ts iter").expect("ts result")
        );
        assert!(timestamp_iter.next().is_none());
        assert_eq!(
            (ms(200), block1.clone()),
            block_iter.next().expect("b iter").expect("b result")
        );
        assert!(block_iter.next().is_none());

        writer.record_values(ms(300), &block2).expect("write");
        let header = reader.load_block_header().expect("load header");
        assert_eq!(ms(300), header.duration());
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
            ms(300),
            timestamp_iter.next().expect("ts iter").expect("ts result")
        );
        assert!(timestamp_iter.next().is_none());
        assert_eq!(
            (ms(300), block2.clone()),
            block_iter.next().expect("b iter").expect("b result")
        );
        assert!(block_iter.next().is_none());
        assert_eq!(
            block1.into_iter().chain(block2).collect::<Vec<_>>(),
            record_iter
                .map(|result| result.expect("r iter").1)
                .collect::<Vec<_>>()
        );
    }
}
