use std::{collections::HashMap, fmt::Display/*, rc::Rc*/};
use parsing::{ast_parser, BinOp, ExecRes, Expression, Function, Literal, MonOp, Statement, TopLevelConstruct};

pub mod parsing;
pub mod common;

use common::error::{InterpreterError, InterpreterErrorType};

pub type IResult<T> = Result<T, InterpreterError>;

#[derive(Debug)]
pub struct Env {
    variables: HashMap<String, Literal>,
    functions: HashMap<String, Function>,
}

#[derive(PartialEq)]
pub enum ExecutionContext {
    Global,
    Function, // Need for a special case for function execution to allow return statements only in those
}

impl Env {
    fn new() -> Self {
        Env {
            variables: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    fn insert_key_default_var(&mut self, key: String) {
        self.variables.insert(key, Literal::Number(0.));
    }

    fn insert_var(&mut self, key: String, val: Literal) {
        self.variables.insert(key, val);
    }

    fn extract_var(&self, key: &String) -> IResult<Literal> {
        self.variables.get(key).cloned().ok_or(InterpreterError::raise(InterpreterErrorType::ValueError))
    }

    fn insert_fn(&mut self, key: String, function: Function) {
        self.functions.insert(key, function);
    }

    // A "jump" is solely a read-only return of the function's code to be executed
    // TODO: remove clone calls
    fn extract_fn(&mut self, key: String) -> IResult<Function> {
        self.functions.get(&key).cloned().ok_or(InterpreterError::raise(InterpreterErrorType::ValueError))
    }
}

pub struct Interpreter {
    env: Env,
    statements: Vec<Statement>,
    context: ExecutionContext,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Env::new(),
            statements: vec![],
            context: ExecutionContext::Global,
        }
    }

    pub fn parse_source(&self, src: &str) -> Result<Vec<Statement>, peg::error::ParseError<peg::str::LineCol>> {
        ast_parser::parse(src)
    }

    pub fn init(&mut self, src: &str) {
        self.statements = 
        match self.parse_source(src) {
            Ok(stmts) => stmts,
            Err(_) => panic!("Parsing failed, syntaxic error!"),
        };
    }

    fn exec_stmts(&mut self, statements: Vec<Statement>) -> IResult<()> {
        for stmt in statements {
            self.execute_statement(stmt)?;
        }
        Ok(())
    }

    pub fn eval_expr(&mut self, expr: &Expression) -> IResult<Literal> {
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
            // !!!
            Expression::FunctionCall { function_name, arguments } => {
                self.eval_fn_call(function_name, &arguments)
            }
            // !!!
            _ => todo!(),
        }
    }

    fn eval_binop(&self, op: BinOp, lhs: Literal, rhs: Literal) -> IResult<Literal> {
        match op {
            BinOp::Plus => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left + right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Minus => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left - right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Mul => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left * right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Div => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Number(left / right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Eq => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left == right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left == right)),
                (Literal::Nil, Literal::Nil) => Ok(Literal::Bool(true)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Lt => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left < right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left < right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Le => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left <= right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left <= right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Gt => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left > right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left > right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Ge => match (lhs, rhs) {
                (Literal::Number(left), Literal::Number(right)) => Ok(Literal::Bool(left >= right)),
                (Literal::String(left), Literal::String(right)) => Ok(Literal::Bool(left >= right)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            _ => unimplemented!(),
        }
    }

    fn eval_monop(&self, op: MonOp, operand: Literal) -> IResult<Literal> {
        match op {
            MonOp::Minus => match operand {
                Literal::Number(n) => Ok(Literal::Number(-n)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            MonOp::Not => match operand {
                Literal::Bool(b) => Ok(Literal::Bool(!b)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
        }
    }

    fn eval_fn_call(&mut self, function_id: String, arguments: &[Expression]) -> IResult<Literal>{
        let Function { params, stmts } = self.env.extract_fn(function_id)?;

        if arguments.len() != params.len() {
            return Err(InterpreterError::raise(InterpreterErrorType::ArgumentCountError));
        }

        let mut arg_vals = vec![];
        
        for arg in arguments {
            arg_vals.push(self.eval_expr(arg)?);
        }

        let mut local_env = Env::new();
        
        for (param, value) in params.iter().zip(arg_vals)  {
            local_env.insert_var(param.clone(), value);
        }

        let old_env = std::mem::replace(&mut self.env, local_env);
        let old_context = std::mem::replace(&mut self.context, ExecutionContext::Function);

        for stmt in stmts {
            match self.execute_statement(stmt)? {
                ExecRes::Normal => continue,
                ExecRes::Result(ret) => {
                    self.env = old_env; // Pop off function stackframe
                    self.context = old_context;
                    return Ok(ret);
                }
            }
        }
        self.env = old_env; // Pop off function stackframe
        self.context = old_context;
        Ok(Literal::Nil)
    }
    
    fn execute_statement(&mut self, stmt: Statement) -> IResult<ExecRes> {
        match stmt {
            Statement::VarDeclare(id) => self.env.insert_key_default_var(id),
            Statement::VarAssign(id, val) => {
                let expr = self.eval_expr(&val)?;
                self.env.insert_var(id, expr);
            },
            Statement::TopLevelConstruct(construct) => match construct {
                TopLevelConstruct::Function(id, params, stmts) => {
                    self.env.insert_fn(id, Function::from(params, stmts));
                }
                TopLevelConstruct::Class(id, stmts) => unimplemented!(),
            }
            // !!!
            Statement::Return(e) => {
                if self.context != ExecutionContext::Function {
                    return Err(InterpreterError::raise(InterpreterErrorType::SyntaxError));
                }
                let ret_expr = self.eval_expr(&e)?;
                return Ok(ExecRes::Result(ret_expr));
            }
            Statement::While { condition, body } => {
                match condition {
                    Expression::Literal(Literal::Bool(b)) => {
                        while b {
                            for i in body.clone() {
                                self.execute_statement(i)?;
                            }
                        }
                    }
                    _ => return Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
                }
            }
            // !!!
            _ => unimplemented!(),
        }
        Ok(ExecRes::Normal)
    }

    // TODO: remove clone calls
    pub fn run(&mut self) -> IResult<()> {
        let statements = self.statements.clone();
        self.exec_stmts(statements)
    }
}

// Show snapshots of the interpreter state
impl Display for Interpreter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let contents = format!("Variable context:\n{:#?}\nStatements at beginning:\n{:#?}\n", self.env, self.statements);
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