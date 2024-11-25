use thiserror::Error;

/// An error that can occur when parsing or evaluating an expr program
#[derive(Error, Debug)]
pub enum ExprError {
    #[error("{0}")]
    ParseError(String),
    #[error("{0}")]
    ExprError(String),
    #[error(transparent)]
    RegexError(#[from] regex::Error),
}

impl From<String> for ExprError {
    fn from(s: String) -> Self {
        ExprError::ExprError(s)
    }
}

pub type Result<T> = std::result::Result<T, ExprError>;

#[macro_export]
macro_rules! bail {
    ($($arg:tt)*) => {
        return Err($crate::ExprError::ExprError(format!($($arg)*)))
    };
}
