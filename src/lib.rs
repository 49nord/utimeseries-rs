extern crate byte_conv;
extern crate cast;
#[macro_use]
extern crate quick_error;

use byte_conv::As;
use std::{fs, io, mem, path, time, u32};
use std::marker::PhantomData;
use std::io::{Seek, Write};

mod err;
mod util;

pub use err::Error;
use util::Tell;

const MAGIC_NUMBER: u32 = 0x01755453;
const HEADER_SIZE: u64 = mem::size_of::<FileHeader>() as u64;

#[derive(Copy, Clone, Debug)]
#[repr(C)]
struct FileHeader {
    /// Magic number, used for sanity checks
    magic_number: u32,

    // Initial time value
    start_delta_s: u64,
    start_delta_ns: u32,

    // Interval inside blocks
    interval_ns: u64,
}

impl FileHeader {
    fn new(start: time::SystemTime, interval: time::Duration) -> Result<Self, Error> {
        let epoch_delta = start
            .duration_since(time::UNIX_EPOCH)
            .map_err(|_| Error::TimeOutOfRange)?;

        Ok(FileHeader {
            magic_number: MAGIC_NUMBER,
            start_delta_s: epoch_delta.as_secs(),
            start_delta_ns: epoch_delta.subsec_nanos(),
            interval_ns: util::duration_ns64(interval).ok_or_else(|| Error::IntervalOutOfRange)?,
        })
    }

    fn interval(&self) -> time::Duration {
        util::ns64_duration(self.interval_ns)
    }

    fn start_time(&self) -> time::SystemTime {
        time::UNIX_EPOCH + time::Duration::new(self.start_delta_s, self.start_delta_ns)
    }
}

#[derive(Debug)]
#[repr(C)]
struct BlockHeader<T> {
    offset_ns: u64,

    _pd: PhantomData<T>,
}

#[derive(Debug)]
struct TimeseriesWriter<T, W> {
    out: W,
    _pd: PhantomData<T>,
}

impl<T: Sized, W> TimeseriesWriter<T, W> {
    #[inline]
    fn entry_size() -> u64 {
        mem::size_of::<T>() as u64
    }

    #[inline]
    fn block_size() -> u64 {
        Self::entry_size()
    }
}

impl<T: Sized + Copy, W: Write> TimeseriesWriter<T, W> {
    fn create(
        mut out: W,
        start: time::SystemTime,
        interval: time::Duration,
    ) -> Result<Self, Error> {
        // write out header
        let header = FileHeader::new(start, interval)?;
        out.write_all(header.as_bytes())?;

        Ok(TimeseriesWriter {
            out,
            _pd: PhantomData::<T>,
        })
    }
}

impl<T: Sized + Copy, W: Write + Seek> TimeseriesWriter<T, W> {
    fn append(mut out: W) -> Result<Self, Error> {
        // get current size by seeking to the end and getting the current pos
        let sz = out.seek(io::SeekFrom::End(0))?;

        // if our file is corrupt (broken header), we return an error
        if sz < HEADER_SIZE {
            return Err(Error::CorruptHeader);
        }

        let data_len = sz - HEADER_SIZE;
        let complete_blocks = data_len - (data_len % Self::block_size());

        // otherwise, seek to insert position, which is after the last
        // correctly written input block
        out.seek(io::SeekFrom::Start(
            HEADER_SIZE + complete_blocks * Self::block_size(),
        ))?;

        Ok(TimeseriesWriter {
            out,
            _pd: PhantomData::<T>,
        })
    }
}
