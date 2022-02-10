use nom::{
    bytes::complete::{tag, take},
    number::complete::be_u64,
};

use crate::bplist::{
    errors::{file_too_short, invalid_header, ParseError},
    types::ParseResult,
    BPList, Header, Object, Trailer, Version,
};

mod v00;

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

pub fn parse(buffer: &[u8]) -> Result<BPList, ParseError> {
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
        let trailer_offset = body_offset + rest.len() - 32;
        let (_, trailer) = parse_trailer(trailing)?;
        debug_assert_eq!(
            trailer_offset,
            trailer.offset_table_offset + (trailer.num_objects * trailer.object_ref_size as usize),
            "Trailer must start immediately after offset table"
        );

        let (_, preferences) = match header.version {
            Version::V00 => v00::parse_body(&trailer, body_offset as _, body),
            Version::V15 => todo!("bplist v1.5 body parsing not implemented!"),
            Version::V16 => todo!("bplist v1.6 body parsing not implemented!"),
        }?;
        Ok(BPList { header, trailer })
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
