extern crate byte_conv;
extern crate cast;
#[macro_use]
extern crate quick_error;

use byte_conv::As;
use std::{fs, io, mem, path, time, u32};
use std::marker::PhantomData;
use std::io::{Read, Seek, Write};

mod err;
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
}

#[derive(Debug)]
struct TimeseriesWriter<T, W> {
    out: W,
    header: FileHeader,
    _pd: PhantomData<T>,
}

impl<T: Sized, W> TimeseriesWriter<T, W> {
    #[inline]
    fn entry_size() -> u64 {
        mem::size_of::<T>() as u64
    }

    #[inline]
    fn block_size(&self) -> u64 {
        self.header.block_size::<T>()
    }

    #[inline]
    pub fn block_length(&self) -> u32 {
        self.header.block_length
    }
}

impl<T: Sized + Copy, W: Write> TimeseriesWriter<T, W> {
    fn create(
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

    fn record_values(&mut self, offset: time::Duration, values: &[T]) -> Result<(), Error> {
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
}

impl<T: Sized + Copy, W: Write + Seek + Read> TimeseriesWriter<T, W> {
    fn append(mut out: W) -> Result<Self, Error> {
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
