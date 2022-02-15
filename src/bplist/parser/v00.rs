//! Implements the body parser for binary plist format (magic bytes `bplist00`)
use std::collections::HashMap;

use nom::{
    combinator::{all_consuming, fail, map},
    number::complete::{be_f32, be_f64, be_i128, be_i64, be_u16, be_u32, be_u8},
    IResult,
};

use crate::bplist::{errors::ParseError, parser::Object, types::ParseResult, Trailer};

trait FromAscii {
    fn from_ascii(_: &[u8]) -> Result<String, FromAsciiError>;
}

struct FromAsciiError;

impl FromAscii for String {
    fn from_ascii(elems: &[u8]) -> Result<String, FromAsciiError> {
        if elems.is_ascii() {
            let mut s = String::with_capacity(elems.len());
            s.extend(elems.iter().map(|&r| r as char));
            Ok(s)
        } else {
            Err(FromAsciiError {})
        }
    }
}

#[derive(Debug, PartialEq)]
enum TypeMarker {
    NullOrBool = 0x00,
    Integer = 0x10,
    Real = 0x20,
    Date = 0x30,
    Data = 0x40,
    AsciiString = 0x50,
    Unicode16String = 0x60,
    Array = 0xA0,
    Dictionary = 0xD0,
}

impl TryFrom<u8> for TypeMarker {
    type Error = ParseError;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x00 => Ok(Self::NullOrBool),
            0x10 => Ok(Self::Integer),
            0x20 => Ok(Self::Real),
            0x30 => Ok(Self::Date),
            0x40 => Ok(Self::Data),
            0x50 => Ok(Self::AsciiString),
            0x60 => Ok(Self::Unicode16String),
            0xA0 => Ok(Self::Array),
            0xD0 => Ok(Self::Dictionary),
            byte => Err(ParseError::InvalidContent(byte)),
        }
    }
}

mod constants {
    pub const BYTE_MARKER_NULL: u8 = 0x00;
    pub const BYTE_MARKER_FALSE: u8 = 0x08;
    pub const BYTE_MARKER_TRUE: u8 = 0x09;
    pub const BYTE_MARKER_DATE: u8 = 0x33;
    /// 0x0f is a special size flag which indicates that the next two bytes
    /// will be an int type marker, and then the size it encodes
    pub const INTEGER_SIZE_FOLLOWS: u8 = 0x0f;
}

use constants::*;

#[derive(Debug)]
struct UnresolvedObject<'a> {
    shell: Object,
    children: Option<&'a [u8]>,
}

impl<'a> UnresolvedObject<'a> {
    /// Wrap an object that cannot have children into this `UnresolvedObject`.
    /// This exists for making creating objects without children more
    /// convenient.
    fn wrap(item: Object) -> Self {
        Self {
            shell: item,
            children: None,
        }
    }

    /// Check if the current object needs to be resolved any further.
    ///
    /// This will only return true if an object has a non-empty collection of
    /// children
    fn needs_resolution(&self) -> bool {
        self.children.map_or(false, |offsets| !offsets.is_empty())
    }
}

fn create_null_or_bool<'buf>(byte: u8) -> Result<UnresolvedObject<'buf>, ParseError> {
    match byte & 0x0f {
        BYTE_MARKER_NULL => Ok(UnresolvedObject::wrap(Object::Null)),
        BYTE_MARKER_TRUE => Ok(UnresolvedObject::wrap(Object::Boolean(true))),
        BYTE_MARKER_FALSE => Ok(UnresolvedObject::wrap(Object::Boolean(false))),
        _ => Err(ParseError::InvalidContent(byte)),
    }
}

/// Parse an integer that is represented in a type that is at least `width`
/// bytes wide. This parser will check if all of the buffer is consumed in the
/// process of creating the integer.
///
/// The plutil tool:
/// 1. Interprets 1, 2, 4 byte integers as unsigned
/// 2. Interprets 8, 16 byte integers are interpreted as signed
/// 3. Fail if numbers wider than 16 bytes are provided
fn create_integer<'buf>(width: u8, data: &'buf [u8]) -> Result<UnresolvedObject<'_>, ParseError> {
    // This is likely better than an `if` because we expect the `width` to be
    // an integer power of 2
    let parser: Box<dyn FnMut(&'buf [u8]) -> IResult<&'_ [u8], Object>> = match width {
        1 => Box::new(map(be_u8, |r| Object::UnsignedInteger(r.into()))),
        2 => Box::new(map(be_u16, |r| Object::UnsignedInteger(r.into()))),
        4 => Box::new(map(be_u32, Object::UnsignedInteger)),
        8 => Box::new(map(be_i64, |r| Object::SignedInteger(r.into()))),
        16 => Box::new(map(be_i128, Object::SignedInteger)),
        _ => Box::new(fail),
    };
    let (_, obj) = all_consuming(parser)(data)
        .map_err(|_| ParseError::InvalidInteger(width, data.to_vec()))?;
    Ok(UnresolvedObject::wrap(obj))
}

/// Parse a floating point number that is represented in a type that is at
/// least `width` bytes wide. This parser will check if all of the buffer is
/// consumed in the process of creating a float.
fn create_realnum<'buf>(width: u8, data: &'buf [u8]) -> Result<UnresolvedObject<'_>, ParseError> {
    let parser: Box<dyn FnMut(&'buf [u8]) -> IResult<&'_ [u8], Object>> = match width {
        4 => Box::new(map(be_f32, |r| Object::Real(r.into()))),
        8 => Box::new(map(be_f64, Object::Real)),
        _ => Box::new(fail),
    };
    let (_, obj) =
        all_consuming(parser)(data).map_err(|_| ParseError::InvalidFloat(width, data.to_vec()))?;
    Ok(UnresolvedObject::wrap(obj))
}

/// Parse a date encoded as a Core Foundation date.
/// Core Foundation dates are stored as 64 bit floating point offsets 31 years
/// after unix epoch (Jan 1, 2001 00:00:00 GMT ). Apple calls timestamps
/// relative to this epoch [`CFAbsoluteTime`][1].
///
/// [1]: https://developer.apple.com/documentation/corefoundation/cfabsolutetime
fn create_date<'buf>(data: &'buf [u8]) -> Result<UnresolvedObject<'_>, ParseError> {
    // NOTE: This name is bound to f64 so that the Error type of be_f64 can be
    // inferred. Without this we end up with E0283
    let read_f64: fn(&'buf [u8]) -> IResult<&'_ [u8], f64> = be_f64;
    let (_, cf_date) =
        all_consuming(read_f64)(data).map_err(|_| ParseError::InvalidDate(data.to_owned()))?;
    const SECONDS_BETWEEN_CF_AND_UNIX_EPOCH: f64 = 978_307_200.0;
    let unix_date_offset: f64 = cf_date + SECONDS_BETWEEN_CF_AND_UNIX_EPOCH;
    Ok(UnresolvedObject::wrap(Object::DateTime(unix_date_offset)))
}

/// Reads arbitrary binary data into a bytebuffer
fn create_data_from_buffer<'buf>(
    size_marker: u8,
    data: &'buf [u8],
) -> Result<UnresolvedObject<'_>, ParseError> {
    let (buffer, num_bytes) = match size_marker {
        INTEGER_SIZE_FOLLOWS => parse_size_marker(size_marker, data),
        num_bytes => Ok((data, num_bytes as usize)),
    }?;
    debug_assert_eq!(
        num_bytes as usize,
        buffer.len(),
        "Number of bytes in size doesn't match buffer size"
    );
    Ok(UnresolvedObject::wrap(Object::Blob(buffer.to_owned())))
}

/// Reads size of a structure encoded in the structures body bytes
fn read_size<'buf>(data: &'buf [u8]) -> ParseResult<&'_ [u8], usize> {
    let width = 1 << (data[0] & 0x0f);
    let content = &data[1..];
    let result: IResult<&'buf [u8], usize> = match width {
        1 => map(be_u8, |r| r as usize)(content),
        2 => map(be_u16, |r| r as usize)(content),
        4 => map(be_u32, |r| r as usize)(content),
        _ => fail(content),
    };

    result.map_err(|_| ParseError::InvalidInteger(width, content[..width.into()].to_vec()))
}

fn parse_size_marker<'buf>(size_marker: u8, data: &'buf [u8]) -> ParseResult<&'_ [u8], usize> {
    match size_marker {
        INTEGER_SIZE_FOLLOWS => read_size(data),
        size => Ok((data, size as usize)),
    }
}

/// Parses the input buffer into an ASCII string. Checks and produces an error
/// if an ASCII string could not be created.
fn create_ascii_string<'buf>(
    size_marker: u8,
    data: &'buf [u8],
) -> Result<UnresolvedObject<'_>, ParseError> {
    let (buffer, num_chars) = parse_size_marker(size_marker, data)?;
    debug_assert_eq!(
        num_chars,
        buffer.len(),
        "Parsed length must be same as length of string being parsed"
    );
    let string =
        String::from_ascii(buffer).map_err(|_| ParseError::InvalidAsciiString(buffer.to_vec()))?;
    Ok(UnresolvedObject::wrap(Object::AsciiString(string)))
}

/// Parses the input buffer into a UTF-16 encoded string.
/// Checks and produces an error if a UTF-16 BE string could not be created.
fn create_utf16_string<'buf>(
    size_marker: u8,
    data: &'buf [u8],
) -> Result<UnresolvedObject<'_>, ParseError> {
    let (buffer, num_chars) = parse_size_marker(size_marker, data)?;
    // Since each char is a `u16`, the number of bytes (`u8`)
    // in the string should be twice the number of chars expected
    debug_assert_eq!(
        2 * num_chars as usize,
        buffer.len(),
        "Parsed length must be same as length of string being parsed"
    );
    // FIXME: Replace with `slice::array_chunks()` once it is stablized
    let chars = buffer
        .chunks(2)
        .map(|w| {
            let bytes: [u8; 2] = w[..3].try_into().expect("Unable to convert slice to array");
            u16::from_be_bytes(bytes)
        })
        .collect::<Vec<_>>();
    let string =
        String::from_utf16(&chars).map_err(|_| ParseError::InvalidUtf16String(buffer.to_vec()))?;
    Ok(UnresolvedObject::wrap(Object::AsciiString(string)))
}

/// Parse the buffer to create a partially initialized array object.
/// This does not recursively parse the child elements but will store
/// offsets to them for resolution at a later time
fn create_array<'buf>(
    size_marker: u8,
    buffer: &'buf [u8],
) -> Result<UnresolvedObject<'buf>, ParseError> {
    let (child_offsets, num_elems) = match size_marker {
        INTEGER_SIZE_FOLLOWS => parse_size_marker(size_marker, buffer),
        num_elems => Ok((buffer, num_elems as usize)),
    }?;
    debug_assert_eq!(
        num_elems,
        buffer.len(),
        "Buffer has incorrect number of array elements"
    );
    Ok(UnresolvedObject {
        shell: Object::Array(Vec::with_capacity(num_elems)),
        children: if !child_offsets.is_empty() {
            Some(child_offsets)
        } else {
            None
        },
    })
}

/// Parse the buffer to create a partially initialized dictionary object.
/// This does not recursively parse the child key-value pairs but will store
/// offsets to them for resolution at a later time
fn create_dictionary<'buf>(
    size_marker: u8,
    buffer: &'buf [u8],
) -> Result<UnresolvedObject<'buf>, ParseError> {
    // Doesn't handle the case of 0xDF
    let (child_offsets, num_pairs) = match size_marker {
        INTEGER_SIZE_FOLLOWS => parse_size_marker(size_marker, buffer),
        num_pairs => Ok((buffer, num_pairs as usize)),
    }?;
    debug_assert_eq!(
        2 * num_pairs,
        child_offsets.len(),
        "Buffer must contain the correct number of K-V pairs"
    );
    Ok(UnresolvedObject {
        shell: Object::Dictionary(HashMap::with_capacity(num_pairs)),
        children: if !child_offsets.is_empty() {
            Some(child_offsets)
        } else {
            None
        },
    })
}

/// Parse the buffer create a partially initialized object. Self referential
/// structures such as Arrays / Dictionaries are partially initialized with
/// the required space to store child objects, but will not attempt to parse
/// the children, since those will be resolved later.
fn create_object_from_buffer<'buf>(
    buffer: &'buf [u8],
) -> Result<UnresolvedObject<'buf>, ParseError> {
    println!("parse ({:02} bytes): {:02x?}", buffer.len(), buffer);
    match buffer.first() {
        Some(&byte) => match (byte & 0xf0).try_into()? {
            TypeMarker::NullOrBool => create_null_or_bool::<'buf>(byte),
            TypeMarker::Integer => {
                let width = 1 << (byte & 0x0f);
                create_integer(width, &buffer[1..])
            }
            TypeMarker::Real => {
                let width = 1 << (byte & 0x0f);
                create_realnum(width, &buffer[1..])
            }
            TypeMarker::Date => match byte {
                BYTE_MARKER_DATE => create_date(&buffer[1..]),
                _ => Err(ParseError::InvalidContent(byte)),
            },
            TypeMarker::Data => create_data_from_buffer(byte & 0x0f, &buffer[1..]),
            TypeMarker::AsciiString => create_ascii_string(byte & 0x0f, &buffer[1..]),
            TypeMarker::Unicode16String => create_utf16_string(byte & 0x0f, &buffer[1..]),
            TypeMarker::Array => create_array(byte & 0x0f, &buffer[1..]),
            TypeMarker::Dictionary => create_dictionary(byte & 0x0f, &buffer[1..]),
        },
        None => Err(ParseError::InvalidDataOffset(1)),
    }
}

#[derive(Debug)]
struct Body<'buf> {
    contents: &'buf [u8],
    offset_table: &'buf [u8],
    body_offset: usize,
    offset_size: usize,
}

impl<'a, 'buf> IntoIterator for &'a Body<'buf> {
    type Item = (usize, &'buf [u8]);
    type IntoIter = BodyIntoIterator<'a, 'buf>;

    fn into_iter(self) -> Self::IntoIter {
        BodyIntoIterator {
            body: self,
            index: 0,
        }
    }
}

#[derive(Debug)]
struct BodyIntoIterator<'a, 'buf: 'a> {
    body: &'a Body<'buf>,
    index: usize,
}

impl<'a, 'buf> Iterator for BodyIntoIterator<'a, 'buf> {
    type Item = (usize, &'buf [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.body.offset_table.len() {
            let lower_offset = self
                .body
                .transform_offset(self.body.offset_table[self.index] as usize);
            let upper_offset = match self.body.offset_table.get(self.index + 1) {
                Some(&off) => self.body.transform_offset(off as usize),
                None => self.body.contents.len(),
            };
            debug_assert!(
                upper_offset > lower_offset,
                "Body chunk range must not be empty"
            );
            self.index += 1;
            Some((
                lower_offset,
                &self.body.contents[lower_offset..upper_offset],
            ))
        } else {
            None
        }
    }
}

impl<'a> Body<'a> {
    /// Return a new body bytes instance
    fn new(buffer: &'a [u8], trailer: &Trailer, body_offset: usize) -> Self {
        // The +1 is to encode the minimum of 1 object (0x00) that can be in a valid plist
        debug_assert!(
            trailer.offset_table_offset > body_offset,
            "Offset table starts before end of body! Offset table: {}, body: {}",
            trailer.offset_table_offset,
            body_offset
        );
        let table_offset = trailer.offset_table_offset - body_offset;
        debug_assert_eq!(
            buffer.len(),
            (table_offset
                + (trailer.num_objects - trailer.top_object_idx) * trailer.offset_size as usize),
            "Buffer length should be equal to offset start table idx + num objects"
        );
        let (content_bytes, offset_table_bytes) = buffer.split_at(table_offset);
        let addressable_offsets = &offset_table_bytes[trailer.top_object_idx..];
        debug_assert_eq!(
            addressable_offsets.len(),
            trailer.num_objects,
            "Number of addressable body offsets is different from number of objects encoded"
        );
        Self {
            contents: content_bytes,
            offset_table: addressable_offsets,
            body_offset,
            offset_size: trailer.offset_size as usize,
        }
    }

    fn transform_offset(&self, offset: usize) -> usize {
        self.offset_size * offset - self.body_offset
    }
}

pub fn parse_body<'a>(
    trailer: &Trailer,
    body_offset: u8,
    buffer: &'a [u8],
) -> ParseResult<&'a [u8], ()> {
    let body = Body::new(buffer, trailer, body_offset as usize);
    let mut object_table: Vec<_> = Vec::with_capacity(trailer.num_objects);

    for (offset, chunk) in &body {
        // Translate the offsets of errors relative to the start of the file
        let partial_obj = create_object_from_buffer(chunk);
        let partial_obj = partial_obj.map_err(|err| match err {
            ParseError::InvalidDataOffset(o) => {
                ParseError::InvalidDataOffset(o + offset + body_offset as usize)
            }
            _ => err,
        })?;
        object_table.push(partial_obj);
    }

    todo!("Resolve objects here");

    unreachable!("Each plist MUST have a root object. How did you get here?");
}
