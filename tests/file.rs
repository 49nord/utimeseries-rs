extern crate tempfile;
extern crate utimeseries;

use std::fs::{File, OpenOptions};
use std::time::{Duration, SystemTime};
use utimeseries::{TimeseriesReader, TimeseriesWriter};

#[test]
fn file() {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("timeseries.log");
    let file = File::create(&path).expect("create file");
    let start = SystemTime::now();
    let new_start = start + Duration::from_secs(10);
    let mut writer =
        TimeseriesWriter::create(file, 2, start, Duration::from_millis(100)).expect("create");
    writer
        .record_values(Duration::from_millis(0), &[1u32, 2u32])
        .expect("record");

    let file2 = File::open(&path).expect("open file");
    let mut block_iter = TimeseriesReader::open(file2)
        .expect("open")
        .into_block_iterator();
    assert_eq!(
        (Duration::from_millis(0), vec![1u32, 2u32]),
        block_iter.next().expect("next").expect("iter result")
    );
    assert!(block_iter.next().is_none());

    writer
        .record_values(Duration::from_millis(200), &[3u32, 4u32])
        .expect("record");
    writer
        .record_values(Duration::from_millis(400), &[5u32, 6u32])
        .expect("record");

    assert!(block_iter.next().is_none());
    block_iter.refresh().expect("refresh");
    assert_eq!(
        (Duration::from_millis(200), vec![3u32, 4u32]),
        block_iter.next().expect("next").expect("iter result")
    );
    assert_eq!(
        (Duration::from_millis(400), vec![5u32, 6u32]),
        block_iter.next().expect("next").expect("iter result")
    );
    assert!(block_iter.next().is_none());

    let file3 = OpenOptions::new()
        .write(true)
        .read(true)
        .open(&path)
        .expect("open file");
    let mut writer2 = TimeseriesWriter::append(file3).expect("append");
    writer2
        .record_values(Duration::from_millis(600), &[7u32, 8u32])
        .expect("record");
    assert_eq!(start, writer2.set_start_time(new_start).expect("set start"));

    assert!(block_iter.next().is_none());
    block_iter.refresh().expect("refresh");
    assert_eq!(
        vec![(Duration::from_millis(600), vec![7u32, 8u32])],
        block_iter.filter_map(Result::ok).collect::<Vec<_>>()
    );

    let file4 = File::open(&path).expect("open file");
    let writer4 = TimeseriesReader::open(file4).expect("open");
    assert_eq!(new_start, writer4.start_time());
    let block_iter = writer4.into_block_iterator();
    assert_eq!(
        vec![
            (Duration::from_millis(0), vec![1u32, 2u32]),
            (Duration::from_millis(200), vec![3u32, 4u32]),
            (Duration::from_millis(400), vec![5u32, 6u32]),
            (Duration::from_millis(600), vec![7u32, 8u32]),
        ],
        block_iter.filter_map(Result::ok).collect::<Vec<_>>()
    );
}
