use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Parse error: {0}")]
    ParseError(String),
    #[error("Eval error: {0}")]
    EvalError(String),
}

pub type Result<T> = std::result::Result<T, Error>;
