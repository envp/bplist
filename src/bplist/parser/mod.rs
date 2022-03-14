use nom::{
    bytes::complete::{tag, take},
    number::complete::be_u64,
};

use crate::bplist::{
    errors::{file_too_short, invalid_header, ParseError},
    types::ParseResult,
    Object, PList,
};

mod v00;

/// Properrty list header, only contains the field
#[derive(Debug, PartialEq)]
struct Header {
    pub version: Version,
}

/// Plist versions that are possible
#[derive(Debug, PartialEq)]
pub enum Version {
    V00,
    V15,
    V16,
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

#[inline]
/// Read the next `N` bytes from the inputs stream, advancing it in the
/// process, returns a sized slice containing the bytes read.
fn take_n<const N: usize>(input: &[u8]) -> ParseResult<&'_ [u8], [u8; N]> {
    let (rest, data) = take(N)(input).map_err(file_too_short(N))?;
    let mut sized_data: [u8; N] = [0; N];
    for (dest, src) in sized_data.iter_mut().zip(data) {
        *dest = *src;
    }
    Ok((rest, sized_data))
}

#[inline]
/// Read a 4 byte word from the input stream, assuming big-endian ordering
fn take_be_u64(input: &[u8]) -> ParseResult<&'_ [u8], u64> {
    be_u64(input).map_err(file_too_short(64))
}

/// Parses the header of a binary plist. These are the 'magic bytes' at the
/// beginning of the binary plist file, uniquely identifying the encoding
/// format used
///
/// Can be one of:
/// - `bplist00`: `[0x62, 0x70, 0x6c, 0x69, 0x73, 0x74, 0x30, 0x30]`
/// - `bplist15`: `[0x62, 0x70, 0x6c, 0x69, 0x73, 0x74, 0x31, 0x35]`
/// - `bplist16`: `[0x62, 0x70, 0x6c, 0x69, 0x73, 0x74, 0x31, 0x36]`
fn parse_header(buffer: &[u8]) -> ParseResult<&'_ [u8], Header> {
    let (rest, _) = tag(b"bplist")(buffer).map_err(invalid_header())?;
    let (rest, version_bytes) = take(2usize)(rest).map_err(file_too_short(2))?;

    let version = match version_bytes {
        b"00" => Ok(Version::V00),
        b"15" => Ok(Version::V15),
        b"16" => Ok(Version::V16),
        _ => Err(ParseError::UnsupportedVersion),
    }?;

    Ok((rest, Header { version }))
}

/// Parse the 'trailer' bytes of a binary plist
fn parse_trailer(buffer: &[u8]) -> ParseResult<&'_ [u8], Trailer> {
    // The first 5 bytes are unused, and they are
    // followed by 3 single byte fields:
    // sort_version, offset_int_size, object_ref_size
    let (rest, _) = take(5usize)(buffer).map_err(file_too_short(5))?;
    let (rest, [sort_version, offset_int_size, object_ref_size]) = take_n::<3>(rest)?;
    let (rest, num_objects) = take_be_u64(rest).map(|(r, word)| (r, word as usize))?;
    let (rest, top_object_idx) = take_be_u64(rest)?;
    let (rest, offset_table_offset) = take_be_u64(rest).map(|(r, word)| (r, word as usize))?;
    Ok((
        rest,
        Trailer {
            sort_version,
            offset_size: offset_int_size,
            object_ref_size,
            num_objects,
            top_object_idx: top_object_idx as usize,
            offset_table_offset,
        },
    ))
}

pub fn parse(buffer: &[u8]) -> Result<PList, ParseError> {
    // The smallest possible plist is the empty object, which is 1 object. Its
    // size comes out to:
    //
    // Part             Num Bytes
    // Header           8
    // Empty object     1
    // Offset Table     1
    // Trailer          32
    // TOTAL            42
    if buffer.len() < 42 {
        Err(ParseError::FileTooShort(42))
    } else {
        let (rest, header) = parse_header(buffer)?;
        let body_offset = buffer.len() - rest.len();
        let (body, trailing) = rest.split_at(rest.len() - 32);
        debug_assert_eq!(
            trailing.len(),
            32,
            "binary plist trailers MUST be 32 bytes long!"
        );
        let trailer_offset = body_offset + body.len();
        let (_, trailer) = parse_trailer(trailing)?;
        dbg!(&trailer);
        debug_assert_eq!(
            trailer_offset,
            trailer.offset_table_offset + (trailer.num_objects * trailer.offset_size as usize),
            "Trailer must start immediately after offset table"
        );

        let body = match header.version {
            Version::V00 => v00::parse_body(&trailer, body_offset as _, body),
            Version::V15 => todo!("bplist v1.5 body parsing not implemented!"),
            Version::V16 => todo!("bplist v1.6 body parsing not implemented!"),
        }?;
        Ok(PList {
            root: body,
            num_objects: trailer.num_objects,
        })
    }
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

    #[cfg(test)]
    mod v00 {
        #[test]
        fn test() {}
    }
}
