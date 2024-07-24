pub type Identifier = String;

#[derive(Debug, PartialEq, PartialOrd)]
pub enum Literal {
    String(String),
    Number(f64),
    Bool(bool),
    Nil
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOp {
    Plus,
    Minus,
    Div,
    Mul,

    And,
    Or,
    XOr,

    Eq,
    Neq,
    Gt,
    Ge,
    Lt,
    Le,
}

// For unary operations only
#[derive(Debug, PartialEq, PartialOrd)]
pub enum MonoOp {
    Minus,
    Not,
}

#[derive(Debug, PartialOrd, PartialEq)]
pub enum Expression {
    Literal(Literal),
    Var(String),
    BinOperation {
        lhs: Box<Expression>,
        rhs: Box<Expression>,
        operator: BinOp,
    },
    UnaryOp {
        operation: MonoOp,
        operand: Box<Expression>,
    },
    FunctionCall {
        function_name: Identifier,
        arguments: Vec<Expression>,
    },
    Object {
        class_name: Identifier,
        arguments: Vec<Expression>,
    }
}