#[derive(Debug)]
pub enum Expr {
    Number(i32),
    String(String),
    Bool(bool),
    Op(Box<Expr>, Opcode, Box<Expr>),
}

#[derive(Debug)]
pub enum Opcode {
    Mul,
    Div,
    Add,
    Sub,
    And,
    Or,
}
