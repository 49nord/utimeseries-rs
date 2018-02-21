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
const NS_PER_S: u64 = 1_000_000_000;

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

        let interval_ns: u64 = interval
            .as_secs()
            .checked_mul(NS_PER_S)
            .and_then(|n| n.checked_add(interval.subsec_nanos() as u64))
            .ok_or_else(|| Error::IntervalOutOfRange)?;

        Ok(FileHeader {
            magic_number: MAGIC_NUMBER,
            start_delta_s: epoch_delta.as_secs(),
            start_delta_ns: epoch_delta.subsec_nanos(),
            interval_ns,
        })
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

        let header = FileHeader::new(start, interval)?;

        // write out header and flush
        out.write_all(header.as_bytes())?;
        out.sync_all()?;

        Ok(TimeseriesWriter {
            _pd: PhantomData::<T>,
        })
    }
}
