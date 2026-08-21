use crate::Rule;
use std::fmt::{self, Debug, Display};

/// An error that can occur when parsing or evaluating an expr program
//
// `Display`, `Error` and the two `From`s are written out rather than derived: `Debug` below
// already is, and a `derive` was the whole reason this crate pulled thiserror into every
// dependent's build for one 20-line enum.
pub enum Error {
    PestError(Box<pest::error::Error<Rule>>),
    ParseError(String),
    ExprError(String),
    #[cfg(feature = "regex")]
    RegexError(regex::Error),
    #[cfg(feature = "serde")]
    DeserializeError(String),
    #[cfg(feature = "serde")]
    SerializeError(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Transparent, as they were: a pest error already says where it is, and prefixing
            // it would bury that.
            Error::PestError(e) => Display::fmt(e, f),
            #[cfg(feature = "regex")]
            Error::RegexError(e) => Display::fmt(e, f),
            Error::ParseError(e) | Error::ExprError(e) => f.write_str(e),
            #[cfg(feature = "serde")]
            Error::DeserializeError(e) | Error::SerializeError(e) => f.write_str(e),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::PestError(e) => Some(e),
            #[cfg(feature = "regex")]
            Error::RegexError(e) => Some(e),
            _ => None,
        }
    }
}

impl From<Box<pest::error::Error<Rule>>> for Error {
    fn from(err: Box<pest::error::Error<Rule>>) -> Self {
        Error::PestError(err)
    }
}

#[cfg(feature = "regex")]
impl From<regex::Error> for Error {
    fn from(err: regex::Error) -> Self {
        Error::RegexError(err)
    }
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Error::ExprError(s)
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::PestError(e) => write!(f, "PestError: {}", e),
            Error::ParseError(e) => write!(f, "ParseError: {}", e),
            Error::ExprError(e) => write!(f, "ExprError: {}", e),
            #[cfg(feature = "regex")]
            Error::RegexError(e) => write!(f, "RegexError: {}", e),
            #[cfg(feature = "serde")]
            Error::DeserializeError(e) => write!(f, "DeserializeError: {}", e),
            #[cfg(feature = "serde")]
            Error::SerializeError(e) => write!(f, "SerializeError: {}", e),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

#[macro_export]
macro_rules! bail {
    ($($arg:tt)*) => {
        return Err($crate::Error::ExprError(format!($($arg)*)))
    };
}
