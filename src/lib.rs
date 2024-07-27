use std::{collections::HashMap, fmt::Display};
use parsing::{ast_parser, BinOp, Expression, Literal, MonOp, Statement};

pub mod parsing;
pub mod common;

use common::error::{InterpreterError, InterpreterErrorType};

pub type IResult<T> = Result<T, InterpreterError<'static>>;

#[derive(Debug)]
pub struct Env {
    variables: HashMap<String, Literal>,
    //top_level_constructs: HashSet<String>,
}

impl Env {
    fn new() -> Self {
        Env {
            variables: HashMap::new(),
        }
    }

    fn insert_key_default_var(&mut self, key: String) {
        self.variables.insert(key, Literal::Number(0.)).unwrap();
    }

    fn insert_var(&mut self, key: String, val: Literal) {
        self.variables.insert(key, val);
    }

    fn extract_var(&self, key: &String) -> IResult<Literal> {
        self.variables.get(key).cloned().ok_or(InterpreterError::raise(&InterpreterErrorType::ValueError))
    }
}

pub struct Interpreter {
    env: Env,
    statements: Vec<Statement>,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Env::new(),
            statements: vec![],
        }
    }

    pub fn parse_source(&self, src: &str) -> Result<Vec<Statement>, peg::error::ParseError<peg::str::LineCol>> {
        ast_parser::parse(src)
    }

    pub fn init(&mut self, src: &str) {
        self.statements = 
        match self.parse_source(src) {
            Ok(stmts) => stmts,
            Err(_) => panic!("Parsing error"),
        };
    }

    fn eval_expr(&self, expr: &Expression) -> IResult<Literal> {
        match expr.clone() {
            Expression::Literal(l) => Ok(l.clone()),
            Expression::Var(id) => self.env.extract_var(&id),
            Expression::BinOperation { lhs, rhs, operator } => {
                let lhs_val = self.eval_expr(&*lhs)?;
                let rhs_val = self.eval_expr(&*rhs)?;
                self.eval_binop(operator, lhs_val, rhs_val)
            },
            Expression::UnaryOp { operation, operand } => {
                let operand_val = self.eval_expr(&*operand)?;
                self.eval_monop(operation, operand_val)
            }
            _ => todo!(),
        }
    }

    fn eval_binop(&self, op: BinOp, lhs: Literal, rhs: Literal) -> IResult<Literal> {
        match op {
            BinOp::Plus => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left + right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Minus => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left - right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Mul => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left * right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Div => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left / right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Eq => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left == right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left == right)),
                (Literal::Nil, Literal::Nil) => Ok(Literal::Bool(true)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Lt => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left < right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left < right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Le => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left <= right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left <= right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Gt => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left > right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left > right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            BinOp::Ge => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left >= right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left >= right)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            _ => unimplemented!(),
        }
    }

    fn eval_monop(&self, op: MonOp, operand: Literal) -> IResult<Literal> {
        match op {
            MonOp::Minus => match operand {
                Literal::Number(n) => Ok(Literal::Number(-n)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
            MonOp::Not => match operand {
                Literal::Bool(b) => Ok(Literal::Bool(!b)),
                _ => Err(InterpreterError::raise(&InterpreterErrorType::TypeError)),
            }
        }
    }

    fn execute_statement(&mut self, stmt: Statement) -> IResult<()> {
        match stmt {
            Statement::VarDeclare(id) => self.env.insert_key_default_var(id),
            Statement::VarAssign(id, val) => self.env.insert_var(id, match val {
                Expression::Literal(l) => l,
                Expression::Var(id) => self.env.extract_var(&id)?,
                _ => unimplemented!(),
            }),
            _ => unimplemented!(),
        }

        Ok(())
    }

    // TODO: remove clone calls
    pub fn run(&mut self) -> IResult<()> {
        let statements = self.statements.clone();
        for stmt in statements{
            self.execute_statement(stmt)?;
        }
        Ok(())
    }
}

// Show snapshots of the interpreter state
impl Display for Interpreter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let contents = format!("Variable context:\n{:#?}\n Statements at beginning:\n{:#?}\n", self.env, self.statements);
        writeln!(f, "{}", contents)
    }
}

#[cfg(test)]
mod tests {
    use crate::{parsing::{Expression, Literal, Statement, TopLevelConstruct}, Interpreter};

    #[test]
    fn parse_var_and_class() {
        let mut interpreter = Interpreter::new();
        let src = "
        var my_var = 12;
        class MyClass {
            var inner = 23;
        }";
        interpreter.init(src);

        assert_eq!(
            interpreter.parse_source(src).unwrap(),
            vec![
                Statement::VarAssign(String::from("my_var"), Expression::Literal(Literal::Number(12.))),
                Statement::TopLevelConstruct(TopLevelConstruct::Class(String::from("MyClass"), vec![
                    Statement::VarAssign(String::from("inner"), Expression::Literal(Literal::Number(23.)))
                ]))
            ]
        );
    }

    #[test]
    fn parse_nested_functions() {
        let mut interpreter = Interpreter::new();
        let src = "
        fun hey() {
            fun ya() {
                var inner_inner = 12;
            }
            var inner = 13;
        }";
        interpreter.init(src);

        assert_eq!(
            interpreter.parse_source(src).unwrap(),
            vec![
                Statement::TopLevelConstruct(TopLevelConstruct::Function(String::from("hey"), vec![], vec![
                    Statement::TopLevelConstruct(TopLevelConstruct::Function(String::from("ya"), vec![], vec![
                        Statement::VarAssign(String::from("inner_inner"), Expression::Literal(Literal::Number(12.)))
                    ])),
                    Statement::VarAssign(String::from("inner"), Expression::Literal(Literal::Number(13.)))
                ]))
            ]
        );
    }
}