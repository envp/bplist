pub type NomErr<Input> = nom::Err<nom::error::Error<Input>>;

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidHeaderTag,
    UnsupportedVersion,
    FileTooShort(usize),
}

#[inline]
pub fn file_too_short<T>(num_bytes: usize) -> impl Fn(NomErr<T>) -> Error {
    move |_: NomErr<_>| Error::FileTooShort(num_bytes)
}

#[inline]
pub fn invalid_header<T>() -> impl Fn(NomErr<T>) -> Error {
    move |_: NomErr<_>| Error::InvalidHeaderTag
}
