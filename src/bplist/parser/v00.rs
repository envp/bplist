use std::collections::HashMap;

use nom::{
    branch::alt,
    combinator::{all_consuming, map},
    number::complete::{be_f32, be_f64, be_i128, be_i64, be_u16, be_u32, be_u64, be_u8},
    IResult,
};

use crate::{
    bplist::{
        errors::{file_too_short, ParseError},
        parser::Object,
        types::ParseResult,
        Trailer,
    },
    parser::TypeMarker,
};

#[derive(Debug)]
struct UnresolvedObject<'a> {
    shell: Object,
    children: Option<&'a [u8]>,
}

impl<'a> UnresolvedObject<'a> {
    fn wrap(item: Object) -> Self {
        Self {
            shell: item,
            children: None,
        }
    }
}

fn create_null_or_bool<'buffer>(byte: u8) -> Result<UnresolvedObject<'buffer>, ParseError> {
    match byte & 0x0f {
        0x00 => Ok(UnresolvedObject::wrap(Object::Null)),
        0x08 => Ok(UnresolvedObject::wrap(Object::Boolean(false))),
        0x09 => Ok(UnresolvedObject::wrap(Object::Boolean(false))),
        _ => Err(ParseError::InvalidContent(byte)),
    }
}

fn parse_at_most_u32<'buffer>(data: &'buffer [u8]) -> IResult<&'buffer [u8], u32> {
    alt((be_u32, map(be_u16, |r| r.into()), map(be_u8, |r| r.into())))(data)
}

fn parse_i64_or_i128<'buffer>(data: &'buffer [u8]) -> IResult<&'buffer [u8], i128> {
    alt((be_i128, map(be_i64, |r| r as i128)))(data)
}

fn parse_at_most_f64<'buffer>(data: &'buffer [u8]) -> IResult<&'buffer [u8], f64> {
    alt((be_f64, map(be_f32, |r| r as f64)))(data)
}

/// Parse an integer that is represented in a type that is at least `width`
/// bytes wide.
/// The plutil tool:
/// 1. Interprets 1, 2, 4 byte integers as unsigned
/// 2. Interprets 8, 16 byte integers are interpreted as signed
/// 3. Fail if numbers wider than 16 bytes are provided
fn create_integer<'buf>(width: u8, data: &'buf [u8]) -> Result<UnresolvedObject<'_>, ParseError> {
    // This is likely better than an `if` because we expect the `width` to be
    // an integer power of 2
    match width {
        1 | 2 | 4 => {
            let (_, number) = all_consuming(parse_at_most_u32)(data)
                .map_err(|_| ParseError::InvalidInteger(data.to_owned()))?;
            Ok(UnresolvedObject::wrap(Object::UnsignedInteger(number)))
        }
        8 | 16 => {
            let (_, number) = all_consuming(parse_i64_or_i128)(data)
                .map_err(|_| ParseError::InvalidInteger(data.to_owned()))?;
            Ok(UnresolvedObject::wrap(Object::SignedInteger(number)))
        }
        _ => Err(ParseError::InvalidIntegerWidth(width)),
    }
}

fn create_realnum<'buf>(width: u8, data: &'buf [u8]) -> Result<UnresolvedObject<'_>, ParseError> {
    match width {
        4 | 8 => {
            let (_, number) = all_consuming(parse_at_most_f64)(data)
                .map_err(|_| ParseError::InvalidFloat(data.to_owned()))?;
            Ok(UnresolvedObject::wrap(Object::Real(number)))
        }
        _ => Err(ParseError::InvalidFloatWidth(width)),
    }
}

fn create_dictionary<'buf>(
    marker: u8,
    buffer: &'buf [u8],
) -> Result<UnresolvedObject<'buf>, ParseError> {
    // Doesn't handle the case of 0xDF
    let (child_offsets, num_pairs) = match marker & 0x0f {
        0x0f => todo!("Implement lookforward for length"),
        num_pairs => (buffer, num_pairs as usize),
    };
    debug_assert_eq!(
        2 * num_pairs,
        child_offsets.len(),
        "Buffer must contain the correct number of K-V pairs"
    );
    Ok(UnresolvedObject {
        shell: Object::Dictionary(HashMap::with_capacity(num_pairs)),
        children: Some(child_offsets),
    })
}

fn create_object_from_buffer<'buffer>(
    buffer: &'buffer [u8],
) -> Result<UnresolvedObject<'buffer>, ParseError> {
    println!("parse ({:02} bytes): {:02x?}", buffer.len(), buffer);
    match buffer.first() {
        Some(&byte) => match (byte & 0xf0).try_into()? {
            TypeMarker::NullOrBool => create_null_or_bool::<'buffer>(byte),
            TypeMarker::Integer => {
                let width = 1 << (byte & 0x0f);
                create_integer(width, &buffer[1..])
            }
            TypeMarker::Real => {
                let width = 1 << (byte & 0x0f);
                create_realnum(width, &buffer[1..])
            }
            TypeMarker::Date => todo!(),
            TypeMarker::Data => todo!(),
            TypeMarker::AsciiString => todo!(),
            TypeMarker::Unicode16String => todo!(),
            TypeMarker::Array => todo!(),
            TypeMarker::Dictionary => create_dictionary(byte, &buffer[1..]),
        },
        None => Err(ParseError::InvalidDataOffset(1)),
    }
}

#[derive(Debug)]
struct Body<'buffer> {
    contents: &'buffer [u8],
    offset_table: &'buffer [u8],
    body_offset: usize,
    offset_size: usize,
}

impl<'a, 'buffer> IntoIterator for &'a Body<'buffer> {
    type Item = (usize, &'buffer [u8]);
    type IntoIter = BodyIntoIterator<'a, 'buffer>;

    fn into_iter(self) -> Self::IntoIter {
        BodyIntoIterator {
            body: self,
            index: 0,
        }
    }
}

#[derive(Debug)]
struct BodyIntoIterator<'a, 'buffer: 'a> {
    body: &'a Body<'buffer>,
    index: usize,
}

impl<'a, 'buffer> Iterator for BodyIntoIterator<'a, 'buffer> {
    type Item = (usize, &'buffer [u8]);

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
            trailer.offset_table_offset >= body_offset + 1,
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
    let mut object_table: HashMap<_, _> = HashMap::with_capacity(trailer.num_objects);

    for (offset, chunk) in &body {
        // Translate the offsets of errors relative to the start of the file
        let partial_obj = create_object_from_buffer(chunk);
        let partial_obj = partial_obj.map_err(|err| match err {
            ParseError::InvalidDataOffset(o) => {
                ParseError::InvalidDataOffset(o + offset + body_offset as usize)
            }
            _ => err,
        })?;
        object_table.insert(offset, partial_obj);
    }

    Ok((buffer, ()))
}