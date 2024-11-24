pub mod errors;
pub(crate) mod ast;
mod value;

use errors::Result;
use lalrpop_util::lalrpop_mod;
use indexmap::IndexMap;
use value::Value;
use crate::ast::Expr;
use crate::errors::Error::EvalError;

lalrpop_mod!(grammar);

type Context = IndexMap<String, String>;

pub struct Parser{
}

pub struct Program{
    code: String,
}

impl Parser{
    pub fn new() -> Self {
        Parser{}
    }

    pub fn compile(&self, code: &str) -> Result<Program> {
        Ok(Program{code: code.to_string()})
    }

    pub fn run(&self, program: &Program, ctx: &Context) -> Result<Value> {
        let expr = grammar::ExprParser::new().parse(&program.code).map_err(|e| errors::Error::ParseError(e.to_string()))?;
        self.parse(expr)
    }

    pub fn eval(&self, code: &str, ctx: &Context) -> Result<Value> {
        let program = self.compile(code)?;
        self.run(&program, ctx)
    }

    fn parse(&self, expr: Box<Expr>) -> Result<Value> {
        match *expr {
            Expr::Number(n) => Ok(n.into()),
            Expr::String(s) => Ok(s.into()),
            Expr::Bool(b) => Ok(b.into()),
            Expr::Op(lhs, op, rhs) => {
                let lhs = self.parse(lhs)?;
                let rhs = self.parse(rhs)?;
                match op {
                    ast::Opcode::Add => match (lhs, rhs) {
                        (Value::Number(lhs), Value::Number(rhs)) => Ok((lhs + rhs).into()),
                        (Value::String(lhs), Value::String(rhs)) => Ok((lhs + &rhs).into()),
                        (lhs, rhs) => Err(EvalError(format!("Invalid operands for +: {lhs:?} and {rhs:?}"))),
                    },
                    ast::Opcode::Sub => match (lhs, rhs) {
                        (Value::Number(lhs), Value::Number(rhs)) => Ok((lhs - rhs).into()),
                        (lhs, rhs) => Err(EvalError(format!("Invalid operands for -: {lhs:?} and {rhs:?}"))),
                    },
                    ast::Opcode::Mul => match (lhs, rhs) {
                        (Value::Number(lhs), Value::Number(rhs)) => Ok((lhs * rhs).into()),
                        (lhs, rhs) => Err(EvalError(format!("Invalid operands for *: {lhs:?} and {rhs:?}"))),
                    },
                    ast::Opcode::Div => match (lhs, rhs) {
                        (Value::Number(lhs), Value::Number(rhs)) => Ok((lhs / rhs).into()),
                        (lhs, rhs) => Err(EvalError(format!("Invalid operands for /: {lhs:?} and {rhs:?}"))),
                    },
                    ast::Opcode::And => match (lhs, rhs) {
                        (Value::Bool(lhs), Value::Bool(rhs)) => Ok((lhs && rhs).into()),
                        (lhs, rhs) => Err(EvalError(format!("Invalid operands for &&: {lhs:?} and {rhs:?}"))),
                    },
                    ast::Opcode::Or => match (lhs, rhs) {
                        (Value::Bool(lhs), Value::Bool(rhs)) => Ok((lhs || rhs).into()),
                        (lhs, rhs) => Err(EvalError(format!("Invalid operands for ||: {lhs:?} and {rhs:?}"))),
                    },
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_str_eq;

    #[test]
    fn arithmetic() {
        assert_str_eq!(eval("2 + 3"), "5");
        assert_str_eq!(eval("2 - 3"), "-1");
        assert_str_eq!(eval("2 * 3"), "6");
        assert_str_eq!(eval("7 / 3"), "2");
        assert_str_eq!(eval(r#""foo" + "bar""#), r#""foobar""#);
        assert_str_eq!(eval(r#"true && false"#), "false");
        assert_str_eq!(eval(r#"true || false"#), "true");
    }

    fn eval(code: &str) -> String {
        let ctx = Context::new();
        let p = Parser::new();
        p.eval(code, &ctx).unwrap().to_string()
    }
}
