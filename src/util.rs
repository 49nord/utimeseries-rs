use std::{mem, slice, time};
use std::io::{self, Read, Seek};

const NS_PER_S: u64 = 1_000_000_000;

/// Convert a duration into a 64-bit nanosecond integer
///
/// Note: `u64::MAX` is a little over 584 years in nanoseconds
pub fn duration_ns64(duration: time::Duration) -> Option<u64> {
    duration
        .as_secs()
        .checked_mul(NS_PER_S)
        .and_then(|n| n.checked_add(duration.subsec_nanos() as u64))
}

#[test]
fn duration_ns64_works_for_valid_values() {
    let duration = time::Duration::new(60, 500);

    assert_eq!(duration_ns64(duration), Some(60_000_000_500));
}

#[test]
fn duration_fails_for_invalid_values() {
    use std::u64;

    let duration = time::Duration::new(u64::MAX / NS_PER_S + 1, 0);
    assert_eq!(duration_ns64(duration), None);

    let duration = time::Duration::new(u64::MAX / NS_PER_S, (NS_PER_S + 1) as u32);
    assert_eq!(duration_ns64(duration), None);
}

/// Convert 64-bit nanosecond integer into duration
pub fn ns64_duration(ns: u64) -> time::Duration {
    // this will never fail, since `time::Duration` is larger than a single u64
    time::Duration::new(ns / NS_PER_S, (ns % NS_PER_S) as u32)
}

#[test]
fn duration_roundtrip_ns64() {
    let duration = time::Duration::new(60, 500);
    assert_eq!(
        time::Duration::new(60, 500),
        ns64_duration(duration_ns64(duration).unwrap())
    )
}

/// Tell (seek) trait
///
/// Implements the commonly used `tell` function that is missing from stdlib
pub trait Tell {
    /// Returns the current position from the start in a stream
    fn tell(&mut self) -> io::Result<u64>;
}

impl<T> Tell for T
where
    T: Seek,
{
    fn tell(&mut self) -> io::Result<u64> {
        self.seek(io::SeekFrom::Current(0))
    }
}

/// Read dumped in-memory data from stream
pub trait ReadFrom: Sized {
    /// Read an item from a reader
    unsafe fn read_from<R: Read>(mut r: R) -> io::Result<Self>;
}

impl<T> ReadFrom for T
where
    T: Sized + Copy,
{
    unsafe fn read_from<R: Read>(mut r: R) -> io::Result<Self> {
        // prepare buffer sized the same as type
        let mut val: T = mem::uninitialized();

        // construct raw slice over `val`
        let buf: &mut [u8] =
            slice::from_raw_parts_mut(&mut val as *mut T as *mut u8, mem::size_of::<T>());

        r.read_exact(buf)?;
        Ok(val)
    }
}
