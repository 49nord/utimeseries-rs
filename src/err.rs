use std::io;

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        Io(err: io::Error) {
            from()
            description("io error")
            display("I/O error: {}", err)
            cause(err)
        }
        IntervalOutOfRange {
            description("interval out of range")
            display("The interval in nanoseconds cannot be represent as an unsigned 64-bit integer")
        }
        TimeOutOfRange {
            description("time out of range")
            display("A time was out of range of acceptable times (before UNIX epoch or too large")
        }
        CorruptHeader {
            description("corrupt header")
            display("The header of the database file is corrupt or not present")
        }
        BlockSizeMismatch(want: u32, have: u32) {
            description("block size mismatch")
            display("Invalid number of items for block. Block length is {} items, but got passed {}"
                    , want, have)
        }
        InvalidPathName {
            description("invalid path name")
            display("A given name or id resulted in an invalid path name")
        }
    }
}
