use std::collections::HashMap;

use crate::bplist::errors::ParseError;

/// A parse result returning either the remaining input, parsed output or
/// the parse error
pub type ParseResult<I, O> = Result<(I, O), ParseError>;

#[derive(Debug, PartialEq)]
pub enum Object {
    Null,
    Boolean(bool),
    UnsignedInteger(u32),
    SignedInteger(i128),
    Real(f64),
    Data(Box<[u8]>),
    String(String),
    Array(Vec<Object>),
    Dictionary(HashMap<String, Object>),
}

#[derive(Debug, PartialEq)]
pub enum Version {
    V00,
    V15,
    V16,
}

#[derive(Debug, PartialEq)]
pub struct Header {
    pub version: Version,
}

/// Binary plist trailer describing how the content is encoded
#[derive(Debug)]
pub struct Trailer {
    pub sort_version: u8,
    /// Number of bytes in the file read for each unit offset in the
    /// offset table. This is useful for large plists, where maximum value
    /// of 255 for an offset isn't enough. This extends the maximum offset
    /// value to 65536
    pub offset_size: u8,
    /// Number of bytes needed for each object reference encoded in a container
    pub object_ref_size: u8,
    /// Number of objects encoded in the file
    pub num_objects: usize,
    /// Index of the top level object, from the start of the offset table
    pub top_object_idx: usize,
    /// Offset of the offset table, from the start of the file. All contained
    /// offsets are also relative to the start of the file
    pub offset_table_offset: usize,
}

#[derive(Debug)]
pub struct BPList {
    pub header: Header,
    pub trailer: Trailer,
}
