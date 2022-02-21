//! Types exported by the crate
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
    DateTime(f64),
    Blob(Vec<u8>),
    AsciiString(String),
    Array(Vec<Object>),
    Dictionary(HashMap<String, Object>),
}

#[derive(Debug)]
pub struct PList {
    pub root: Object,
    pub num_objects: usize,
}
