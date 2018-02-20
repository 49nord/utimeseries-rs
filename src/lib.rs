use std::{fs, io, path};
use std::marker::PhantomData;

const MAGIC_NUMBER: u32 = 0x01755453;

#[derive(Debug)]
#[repr(C)]
struct FileHeader<T> {
    /// Magic number, used for sanity checks
    magic_number: u32,

    // Initial time value
    start_time_s: u64,
    start_time_ns: u32,

    // Interval inside blocks
    interval_ns: u32,

    _pd: PhantomData<T>,
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

impl<T> TimeseriesWriter<T> {
    fn create<P: AsRef<path::Path>>(dest: P) -> io::Result<Self> {
        let mut out = fs::File::create(dest)?;

        let header = {
            FileHeader {
                magic_number: MAGIC_NUMBER,
                start_time_s: 0,
                start_time_ns: 0,
                interval_ns: 0,
                _pd: PhantomData::<T>,
            }
        };

        unimplemented!()
        // out.write_all()
    }
}
