use super::{Error, TimeseriesReader, TimeseriesWriter};
use std::{fs, path, time};

#[derive(Debug)]
pub struct TimeseriesDatabase {
    base_path: path::PathBuf,
}

impl TimeseriesDatabase {
    #[inline]
    pub fn new<P: AsRef<path::Path>>(p: P) -> TimeseriesDatabase {
        TimeseriesDatabase {
            base_path: p.as_ref().to_owned(),
        }
    }

    #[inline]
    pub fn create<T: Copy>(
        &self,
        name: &str,
        block_length: u32,
        start: time::SystemTime,
        interval: time::Duration,
    ) -> Result<TimeseriesWriter<T, fs::File>, Error> {
        let file = fs::File::create(self.data_file_path(name)?)?;
        TimeseriesWriter::create(file, block_length, start, interval)
    }

    #[inline]
    pub fn append<T: Copy>(&self, name: &str) -> Result<TimeseriesWriter<T, fs::File>, Error> {
        let file = fs::OpenOptions::new()
            .append(true)
            .read(true)
            .open(self.data_file_path(name)?)?;
        TimeseriesWriter::append(file)
    }

    #[inline]
    pub fn read<T: Copy>(&self, name: &str) -> Result<TimeseriesReader<T, fs::File>, Error> {
        let file = fs::File::open(self.data_file_path(name)?)?;
        TimeseriesReader::open(file)
    }

    fn data_file_path<'a>(&self, name: &'a str) -> Result<&'a path::Path, Error> {
        let mut chars = name.chars();

        // ensure the first char exists, that is name is not an empty string
        let first_char = chars.next().ok_or(Error::InvalidPathName)?;

        // verify [a-zA-Z][a-zA-Z0-9_]
        if !first_char.is_ascii() || !first_char.is_alphabetic() {
            return Err(Error::InvalidPathName);
        }

        for c in chars {
            if !c.is_ascii() {
                return Err(Error::InvalidPathName);
            }

            if !(c.is_alphanumeric() || c == '_') {
                return Err(Error::InvalidPathName);
            }
        }

        Ok(path::Path::new(name))
    }
}
