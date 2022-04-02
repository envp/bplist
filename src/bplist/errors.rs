pub type NomErr<Input> = nom::Err<nom::error::Error<Input>>;

#[derive(Debug, PartialEq)]
pub enum ParseError {
    /// Input ended too soon.
    FileTooShort(usize),

    /// The byte sequence cannot represent a valid ASCII string.
    InvalidAsciiString(Vec<u8>),

    /// An out of bounds error upon using one of the offsets derived from the
    /// buffer.
    InvalidDataOffset(usize),

    /// The serialized date object cannot be parsed.
    ///
    /// Potential reasons include:
    /// * Buffer length doesn't match 4 bytes.
    /// * Buffer doesn't contain a valid `f64`
    InvalidDate(Vec<u8>),

    /// The serialized floating point number could not be parsed.
    ///
    /// Potential reasons include:
    /// * Wrong width (something other than 1, 2, or 4.
    /// * The number of bytes didn't match what the width indicated.
    /// * The buffer could not be parsed into a floating point number.
    InvalidFloat(u8, Vec<u8>),

    /// The file header was not recognized.
    InvalidHeaderTag,

    /// The serialized integer could not be read. This is most likely due to
    /// the width not matching the number of bytes.
    InvalidInteger(u8, Vec<u8>),

    /// Expected a null or bool due to high 4 bits being 0x0, but could not
    /// match the low 4 bits with any of `null` (`0x00`), `true` (`0x07`),
    /// or `false` (`0x08`).
    InvalidNullOrBool(u8),

    /// The prefix (4 bits) could not be recognized.
    InvalidPrefix(u8),

    /// The byte sequence cannot represent a valid UTF-16 string.
    InvalidUtf16String(Vec<u8>),

    /// 0x33 is the date marker. This is used when the parser sees a 0x30 in
    /// the high 4 bits, but sees something other than 0x03 in the lower 4 bits.
    MissingDateMarker(u8),

    /// Generic nom error that has not yet been classified.
    NomError,

    /// The property list version is not yet supported by the library.
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
