# utimeseries

The utimeseries crate is an experimental time series database that uses a fairly compact storage format to record data that occurs in regular intervals. Its primary purpose is to record data such as measurements on embedded devices. The data format is designed with the following goals in mind:

* Corruption resistant: Incomplete or interrupted data-writes will never cause the file to become corrupted
* Fast retrieval: Retrieving a subset of the data should be fast
* Compact

`utimeseries` is currently not published on crates.io, as some ergonomic features are still missing.
