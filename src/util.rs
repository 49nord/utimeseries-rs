use std::time;

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
