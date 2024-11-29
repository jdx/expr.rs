//!
//! Example:
//! ```
//! use expr::{Context, Parser};
//!
//! let mut p = Parser::new();
//!
//! let mut ctx = Context::default();
//! ctx.insert("two".to_string(), 2);
//!
//! let three: i64 = p.eval("1 + two", &ctx).unwrap().as_number().unwrap();
//! assert_eq!(three, 3);
//!
//! p.add_function("add", |c| {
//!   let mut sum = 0;
//!   for arg in c.args {
//!     sum += arg.as_number().unwrap();
//!   }
//!   Ok(sum.into())
//! });
//!
//! let six: i64 = p.eval("add(1, two, 3)", &ctx).unwrap().as_number().unwrap();
//! assert_eq!(six, 6);
//! ```
mod ast;
mod context;
mod error;
mod functions;
mod parser;
mod pest;
mod pratt;
#[cfg(test)]
mod test;
mod value;

pub use crate::context::Context;
pub use crate::error::{Error, Result};
pub use crate::parser::Parser;
pub use crate::value::Value;

pub(crate) use crate::pest::Rule;
