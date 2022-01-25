use crate::bplist::errors::file_too_short;
use crate::bplist::parser::ParseResult;
use nom::{bytes::complete::take, number::complete::be_u64};

#[inline]
pub fn take_n<const N: usize>(input: &[u8]) -> ParseResult<&'_ [u8], [u8; N]> {
    let (rest, data) = take(N)(input).map_err(file_too_short(N))?;
    let mut sized_data: [u8; N] = [0; N];
    for (dest, src) in sized_data.iter_mut().zip(data) {
        *dest = *src;
    }
    Ok((rest, sized_data))
}

#[inline]
pub fn take_be_u64(input: &[u8]) -> ParseResult<&'_ [u8], u64> {
    be_u64(input).map_err(file_too_short(64))
}
