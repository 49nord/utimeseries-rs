extern crate byte_conv;
extern crate cast;
#[macro_use]
extern crate quick_error;

use byte_conv::As;
use std::{fs, io, path, time, u32};
use std::marker::PhantomData;
use std::io::Write;

mod err;
mod util;

pub use err::Error;

const MAGIC_NUMBER: u32 = 0x01755453;

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
struct TimeseriesWriter<T> {
    _pd: PhantomData<T>,
}

impl<T: Sized + Copy> TimeseriesWriter<T> {
    fn create<P: AsRef<path::Path>>(
        dest: P,
        start: time::SystemTime,
        interval: time::Duration,
    ) -> Result<Self, Error> {
        let mut out = fs::File::create(dest)?;

        // write out header and flush
        let header = FileHeader::new(start, interval)?;
        out.write_all(header.as_bytes())?;
        out.sync_all()?;

        Ok(TimeseriesWriter {
            _pd: PhantomData::<T>,
        })
    }
}
