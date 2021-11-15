#[allow(dead_code)]
#[allow(unused)]

mod bplist {
    use nom::{
        bytes::complete::{tag, take},
        error::ParseError,
        number::complete::be_u64,
        sequence::{preceded, tuple},
    };

    type NomErr<Input> = nom::Err<nom::error::Error<Input>>;

    #[derive(Debug)]
    pub enum Error {
        InvalidHeaderTag,
        BadVersionBytes,
        FileTooShort(usize),
    }

    #[derive(Debug)]
    pub enum Version {
        V00,
        V15,
        V16,
    }

    #[derive(Debug)]
    pub struct Header {
        version: Version,
    }

    #[derive(Debug)]
    pub struct Trailer {
        num_objects: usize,
        top_object: u64,
        offset_table_offset: usize,
    }

    #[derive(Debug)]
    pub struct BPList {}

    #[inline]
    fn take_n<const N: usize>(input: &[u8]) -> Result<(&'_ [u8], [u8; N]), Error> {
        let (rest, data) = take(N)(input).map_err(|_: NomErr<&'_ [u8]>| Error::FileTooShort(N))?;
        let mut sized_data: [u8; N] = [0; N];
        for (dest, src) in sized_data.iter_mut().zip(data) {
            *dest = *src;
        }
        Ok((rest, sized_data))
    }

    fn get_be_u64(input: &[u8]) -> Result<(&'_ [u8], u64), Error> {
        be_u64(input).map_err(|_: NomErr<&'_ [u8]>| Error::FileTooShort(64))
    }

    fn parse_header(buffer: &[u8]) -> Result<(&'_ [u8], Header), Error> {
        let (rest, head) =
            tag(b"bplist")(buffer).map_err(|_: NomErr<&'_ [u8]>| Error::InvalidHeaderTag)?;
        let (rest, version_bytes) =
            take(2usize)(rest).map_err(|_: NomErr<&'_ [u8]>| Error::FileTooShort(2))?;

        let version = match version_bytes {
            b"00" => Ok(Version::V00),
            b"15" => Ok(Version::V15),
            b"16" => Ok(Version::V16),
            _ => Err(Error::BadVersionBytes),
        }?;

        Ok((rest, Header { version }))
    }

    fn parse_trailer(buffer: &[u8]) -> Result<(&'_ [u8], Trailer), Error> {
        // The first 5 bytes are unused, and they are
        // followed by 3 single byte fields:
        // sort_version, offset_int_size, object_ref_size
        let (rest, _) = take_n::<8>(buffer)?;
        let (rest, num_objects) = get_be_u64(rest).map(|(r, word)| (r, word as usize))?;
        let (rest, top_object) = get_be_u64(rest)?;
        let (rest, offset_table_offset) = get_be_u64(rest).map(|(r, word)| (r, word as usize))?;
        Ok((
            rest,
            Trailer {
                num_objects,
                top_object,
                offset_table_offset,
            },
        ))
    }

    fn parse_body(trailer: Trailer, buffer: &[u8]) -> Result<(&'_ [u8], ()), Error> {
        println!("{:02x?}", buffer.split_at(trailer.offset_table_offset));
        Ok((buffer, ()))
    }

    pub fn parse(buffer: &[u8]) -> Result<BPList, Error> {
        let (rest, head) = parse_header(buffer)?;
        println!("{:?}", head);

        let (_, trailing) = rest.split_at(rest.len() - 32);
        assert_eq!(trailing.len(), 32, "binary plist trailers MUST be 32 bytes long!");

        let (rest, trailer) = parse_trailer(trailing)?;
        assert!(rest.is_empty(), "");
        println!("{:?}", trailer);

        let (rest, body) = parse_body(trailer, buffer)?;
        println!("{:?}", body);

        Ok(BPList {})
    }
}

use bplist::*;

fn main() {
    let data = include_bytes!("../example.plist");
    let _ = parse(data);
}
