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

#[test]
fn test_tell_works_after_write() {
    use std::io::{Cursor, Write};

    let mut buf = Cursor::new(vec![0; 20]);

    assert_eq!(0, buf.tell().unwrap());

    buf.write_all(b"asdf").unwrap();
    assert_eq!(4, buf.tell().unwrap());

    buf.write_all(b"qq").unwrap();
    assert_eq!(6, buf.tell().unwrap());
}

#[test]
fn test_tell_works_after_seek() {
    use std::io::{Cursor, SeekFrom};

    let mut buf = Cursor::new(vec![0; 20]);

    assert_eq!(0, buf.tell().unwrap());

    buf.seek(SeekFrom::Start(10)).unwrap();

    assert_eq!(10, buf.tell().unwrap());

    buf.seek(SeekFrom::End(0)).unwrap();

    assert_eq!(20, buf.tell().unwrap());
}

pub trait ReadRaw {
    unsafe fn read_raw<T: Copy + Sized>(&mut self) -> io::Result<T>;
}

impl<R: Read> ReadRaw for R {
    unsafe fn read_raw<T: Copy + Sized>(&mut self) -> io::Result<T> {
        // prepare buffer sized the same as type
        let mut val: T = mem::uninitialized();

        // construct raw slice over `val`
        let buf: &mut [u8] =
            slice::from_raw_parts_mut(&mut val as *mut T as *mut u8, mem::size_of::<T>());

        self.read_exact(buf)?;
        Ok(val)
    }
}

#[test]
fn test_read_raw_roundtrip() {
    use std::io::{Cursor, SeekFrom, Write};
    use byte_conv::As;

    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    struct TestStruct {
        v1: u32,
        v2: bool,
    }

    let orig = TestStruct {
        v1: 0x1122FF77,
        v2: true,
    };

    let mut buf = Cursor::new(vec![0; 20]);
    buf.write_all(orig.as_bytes()).unwrap();

    buf.seek(SeekFrom::Start(0)).unwrap();

    let snd: TestStruct = unsafe { buf.read_raw() }.unwrap();

    assert_eq!(snd, orig);
}

// FIXME: maybe move this to itertools?
macro_rules! iter_try {
    ($e: expr) => (match $e {
        Ok(v) => v,
        Err(e) => return Some(Err(e.into())),
    })
}
