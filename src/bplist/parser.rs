use nom::bytes::complete::{tag, take};

use crate::bplist::combinators::{take_be_u64, take_n};
use crate::bplist::errors::{file_too_short, invalid_header, Error};

pub type ParseResult<I, O> = Result<(I, O), Error>;

#[derive(Debug, PartialEq)]
pub enum Version {
    V00,
    V15,
    V16,
}

#[derive(Debug, PartialEq)]
pub struct Header {
    version: Version,
}

#[derive(Debug)]
pub struct Metadata {
    sort_version: u8,
    offset_int_size: u8,
    object_ref_size: u8,
    num_objects: usize,
    top_object: u64,
    offset_table_offset: usize,
}

#[derive(Debug)]
pub struct BPList {
    header: Header,
    trailer: Metadata,
}

fn parse_header(buffer: &[u8]) -> ParseResult<&'_ [u8], Header> {
    let (rest, _) = tag(b"bplist")(buffer).map_err(invalid_header())?;
    let (rest, version_bytes) = take(2usize)(rest).map_err(file_too_short(2))?;

    let version = match version_bytes {
        b"00" => Ok(Version::V00),
        b"15" => Ok(Version::V15),
        b"16" => Ok(Version::V16),
        _ => Err(Error::UnsupportedVersion),
    }?;

    Ok((rest, Header { version }))
}

fn parse_metadata(buffer: &[u8]) -> ParseResult<&'_ [u8], Metadata> {
    // The first 5 bytes are unused, and they are
    // followed by 3 single byte fields:
    // sort_version, offset_int_size, object_ref_size
    let (rest, _) = take(5usize)(buffer).map_err(file_too_short(5))?;
    let (rest, [sort_version, offset_int_size, object_ref_size]) = take_n::<3>(rest)?;
    let (rest, num_objects) = take_be_u64(rest).map(|(r, word)| (r, word as usize))?;
    let (rest, top_object) = take_be_u64(rest)?;
    let (rest, offset_table_offset) = take_be_u64(rest).map(|(r, word)| (r, word as usize))?;
    Ok((
        rest,
        Metadata {
            sort_version,
            offset_int_size,
            object_ref_size,
            num_objects,
            top_object,
            offset_table_offset,
        },
    ))
}

fn parse_body<'a>(
    metadata: &Metadata,
    body_offset: usize,
    buffer: &'a [u8],
) -> ParseResult<&'a [u8], ()> {
    debug_assert_eq!(
        buffer.len(),
        metadata.offset_table_offset - body_offset + metadata.num_objects,
        "Buffer length should be equal to offset table idx + num objects"
    );
    let table_start_idx = metadata.offset_table_offset - body_offset;
    let (items, offset_table) = buffer.split_at(table_start_idx);
    println!("data = {:02x?}", items);
    println!("offset_table = {:02x?}", offset_table);
    Ok((buffer, ()))
}

pub fn parse(buffer: &[u8]) -> Result<BPList, Error> {
    let (rest, header) = parse_header(buffer)?;
    const BODY_OFFSET: usize = 8;
    let (body, trailing) = rest.split_at(rest.len() - 32);
    debug_assert_eq!(
        trailing.len(),
        32,
        "binary plist trailers MUST be 32 bytes long!"
    );

    println!("trailer = {:02x?}", &trailing);
    let (_, metadata) = parse_metadata(trailing)?;
    let (_, preferences) = parse_body(&metadata, BODY_OFFSET, body)?;
    println!("preferences = {:?}", preferences);

    Ok(BPList {
        header,
        trailer: metadata,
    })
}

#[cfg(test)]
mod tests {
    use super::{parse_header, Header, Version};

    #[test]
    fn recognizes_v00_header() {
        let result = parse_header(b"bplist00");
        assert!(result.is_ok());
        if let Ok((rest, header)) = result {
            assert_eq!(
                header,
                Header {
                    version: Version::V00
                }
            );
            assert_eq!(rest, b"");
        } else {
            unreachable!("Failed to parse header. Error: {:?}", result);
        };
    }

    #[test]
    fn recognizes_v15_header() {
        let result = parse_header(b"bplist15");
        assert!(result.is_ok());
        if let Ok((rest, header)) = result {
            assert_eq!(
                header,
                Header {
                    version: Version::V15
                }
            );
            assert_eq!(rest, b"");
        } else {
            unreachable!("Failed to parse header. Error: {:?}", result);
        };
    }

    #[test]
    fn recognizes_v16_header() {
        let result = parse_header(b"bplist16");
        assert!(result.is_ok());
        if let Ok((rest, header)) = result {
            assert_eq!(
                header,
                Header {
                    version: Version::V16
                }
            );
            assert_eq!(rest, b"");
        } else {
            unreachable!("Failed to parse header. Error: {:?}", result);
        };
    }
}
