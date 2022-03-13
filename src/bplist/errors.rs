pub type NomErr<Input> = nom::Err<nom::error::Error<Input>>;

#[derive(Debug, PartialEq)]
pub enum ParseError {
    FileTooShort(usize),
    InvalidAsciiString(Vec<u8>),
    InvalidDataOffset(usize),
    InvalidDate(Vec<u8>),
    InvalidFloat(u8, Vec<u8>),
    InvalidHeaderTag,
    InvalidInteger(u8, Vec<u8>),
    InvalidNullOrBool(u8),
    InvalidPrefix(u8),
    InvalidUtf16String(Vec<u8>),
    MissingDateMarker(u8),
    // FIXME: Rework error reporting for more detailed error markers
    // possible to use error_chain ?
    NomError,
    UnsupportedVersion,
}

#[inline]
pub fn file_too_short<T>(num_bytes: usize) -> impl Fn(NomErr<T>) -> ParseError {
    move |_: NomErr<_>| ParseError::FileTooShort(num_bytes)
}

#[inline]
pub fn invalid_header<T>() -> impl Fn(NomErr<T>) -> ParseError {
    move |_: NomErr<_>| ParseError::InvalidHeaderTag
}

impl<T> From<nom::Err<T>> for ParseError {
    fn from(_: nom::Err<T>) -> Self {
        Self::NomError
    }
}
