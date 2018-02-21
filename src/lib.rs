extern crate byte_conv;
extern crate cast;
#[macro_use]
extern crate quick_error;

use byte_conv::As;
use std::{fs, io, path, time, u32};
use std::marker::PhantomData;
use std::io::Write;

mod err;

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
    interval_ns: u32,
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

        let epoch_delta = start
            .duration_since(time::UNIX_EPOCH)
            .map_err(|_| Error::TimeOutOfRange)?;

        let interval_s: u32 = cast::u32(interval.as_secs()).map_err(|e| Error::IntervalOutOfRange)?;
        let interval_ns: u32 = cast::u32(interval.as_secs())
            .ok()
            .and_then(|n| n.checked_mul(1_000_000_000))
            .and_then(|n| n.checked_add(interval_s))
            .ok_or_else(|| Error::IntervalOutOfRange)?;

        let header = {
            FileHeader {
                magic_number: MAGIC_NUMBER,
                start_delta_s: epoch_delta.as_secs(),
                start_delta_ns: epoch_delta.subsec_nanos(),
                interval_ns,
            }
        };

        // write out header and flush
        out.write_all(header.as_bytes())?;
        out.sync_all()?;

        Ok(TimeseriesWriter {
            _pd: PhantomData::<T>,
        })
    }
}
