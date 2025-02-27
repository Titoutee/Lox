use std::fmt::Display;

pub type Identifier = String;

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum Literal {
    String(String),
    Number(f64),
    Bool(bool),
    Nil
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::String(s) => writeln!(f, "{}", s),
            Literal::Number(n) => writeln!(f, "{}", n),
            Literal::Bool(b) => writeln!(f, "{}", b),
            _ => write!(f, ""),
        }
    }
}

// Any binary operation
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum BinOp {
    Plus,
    Minus,
    Div,
    Mul,

    And,
    Or,
    XOr,

    Eq,
    Neq, // 
    Gt,
    Ge,
    Lt,
    Le,
}

// For unary operations only
#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum MonOp {
    Minus,
    Not,
}

#[derive(Debug, PartialOrd, PartialEq, Clone)]
pub enum Expression {
    Literal(Literal),
    Var(String),
    BinOperation {
        lhs: Box<Expression>,
        rhs: Box<Expression>,
        operator: BinOp,
    },
    UnaryOp {
        operation: MonOp,
        operand: Box<Expression>,
    },
    FunctionCall {
        function_name: Identifier,
        arguments: Vec<Expression>,
    },
    Object {
        class_name: Identifier,
    },
}
