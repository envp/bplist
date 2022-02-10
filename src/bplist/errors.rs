pub type NomErr<Input> = nom::Err<nom::error::Error<Input>>;

#[derive(Debug, PartialEq)]
pub enum ParseError {
    InvalidHeaderTag,
    UnsupportedVersion,
    FileTooShort(usize),
    InvalidContent(u8),
    InvalidDataOffset(usize),
    InvalidIntegerWidth(u8),
    InvalidFloatWidth(u8),
    InvalidInteger(Vec<u8>),
    InvalidDate(Vec<u8>),
    InvalidFloat(Vec<u8>),
    // FIXME: Rework error reporting for more detailed error markers
    NomError,
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
