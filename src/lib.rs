use std::{collections::HashMap, fmt::Display/*, rc::Rc*/};

pub mod parsing;
pub mod common;

use parsing::{ast_parser, expression, BinOp, ExecRes, Expression, Function, Literal, MonOp, Statement, TopLevelConstruct};
use common::error::{InterpreterError, InterpreterErrorType};

pub type IResult<T> = Result<T, InterpreterError>;

#[derive(Debug, Clone)]
pub struct Env {
    variables: Vec<HashMap<String, Literal>>,
    functions: Vec<HashMap<String, Function>>,
}

#[derive(PartialEq, Debug)]
pub enum ExecCtxt {
    Global,
    Function, // Return statements should only exist as part of functions
}

impl Env {
    fn new() -> Self {
        Env {
            variables: vec![HashMap::new()],
            functions: vec![HashMap::new()],
        }
    }

    fn scope_push(&mut self) {
        self.variables.push(HashMap::new());
        self.functions.push(HashMap::new());
    }

    fn scope_pop(&mut self) {
        self.variables.pop();
        self.functions.pop();
    }

    fn insert_key_default_var(&mut self, key: String) {
        if let Some(current_scope) = self.variables.last_mut() {
            current_scope.insert(key, Literal::Number(0.));
        }
        
    }

    fn insert_var(&mut self, key: String, val: Literal) {
        if let Some(current_scope) = self.variables.last_mut() {
            current_scope.insert(key, val).map(|_| ());
        }
    }

    fn reassign_var(&mut self, key: &String, val: Literal) -> Option<()> {
        for scope in self.variables.iter_mut().rev() {
            if let Some(v) = scope.get_mut(key) {
                *v = val;
                return Some(());
            }
        }
        None
    }

    // TODO: remove clone calls
    fn extract_var(&self, key: &String) -> IResult<Literal> {
        for scope in self.variables.iter().rev() {
            if let Some(val) = scope.get(key) {
                return Ok(val.clone());
            }
        }
        Err(InterpreterError::raise(InterpreterErrorType::ValueError))
    }

    fn insert_fn(&mut self, key: String, function: Function) {
        if let Some(current_scope) = self.functions.last_mut() {
            current_scope.insert(key, function);
        }
    }

    // TODO: remove clone calls
    fn extract_fn(&mut self, key: &String) -> IResult<Function> {
        for scope in self.functions.iter().rev() {
            if let Some(val) = scope.get(key) {
                return Ok(val.clone());
            }
        }
        Err(InterpreterError::raise(InterpreterErrorType::ValueError))
    }
}

pub struct Interpreter {
    env: Env,
    statements: Vec<Statement>,
    context: ExecCtxt,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Env::new(),
            statements: vec![],
            context: ExecCtxt::Global,
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

    // Setup a new environment (within a function or a control logic block)
    fn scope_switch(&mut self, new_env: Env) -> Env {
        std::mem::replace(&mut self.env, new_env)
    }

    fn scope_push(&mut self) {
        self.env.scope_push();
    }

    fn scope_pop(&mut self) {
        self.env.scope_pop();
    }

    fn exec_stmts(&mut self, statements: Vec<Statement>) -> IResult<()> {
        for stmt in statements {
            self.execute_statement(stmt)?;
        }
        Ok(())
    }

    /// Main routine for flattening expression until a Literal is yielded.
    // TODO: remove clone calls
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
            Expression::FunctionCall { function_name, arguments } => {
                self.eval_fn_call(function_name, &arguments)
            }
            _ => unimplemented!(),
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
            BinOp::And => match (lhs, rhs) {
                (Literal::Bool(b1), Literal::Bool(b2)) => Ok(Literal::Bool(b1 && b2)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::Or => match (lhs, rhs) {
                (Literal::Bool(b1), Literal::Bool(b2)) => Ok(Literal::Bool(b1 || b2)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
            BinOp::XOr | BinOp::Neq => match (lhs, rhs) {
                (Literal::Bool(b1), Literal::Bool(b2)) => Ok(Literal::Bool(b1 != b2)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
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

    // TODO: remove clone calls
    fn eval_fn_call(&mut self, function_id: String, arguments: &[Expression]) -> IResult<Literal>{
        let Function { params, stmts } = self.env.extract_fn(&function_id)?;

        if arguments.len() != params.len() {
            return Err(InterpreterError::raise(InterpreterErrorType::ArgumentCountError));
        }

        let mut arg_vals = vec![];
        
        for arg in arguments {
            arg_vals.push(self.eval_expr(arg)?);
        }

        let mut local_env = Env::new(); // A new stackframe, as an environment
        
        for (param, value) in params.iter().zip(arg_vals)  {
            local_env.insert_var(param.clone(), value);
        }

        // Recursive behaviour
        local_env.insert_fn(function_id, Function { params, stmts: stmts.clone() });

        let old_env = self.scope_switch(local_env);
        let old_context = std::mem::replace(&mut self.context, ExecCtxt::Function);

        for stmt in stmts {
            match self.execute_statement(stmt)? {
                ExecRes::Normal => (),
                ExecRes::Result(ret) => {
                    self.scope_switch(old_env); // Pop off function stackframe
                    self.context = old_context;
                    return Ok(ret); // Exit early out of function
                }
            }
        }
        self.scope_switch(old_env); // Pop off function stackframe
        self.context = old_context;
        Ok(Literal::Nil)
    }
    
    fn execute_statement(&mut self, stmt: Statement) -> IResult<ExecRes> {
        match stmt {
            Statement::VarDeclare(id) => self.env.insert_key_default_var(id),
            Statement::VarAssign(id, val) => {
                let val = self.eval_expr(&val)?;
                self.env.insert_var(id, val);
            },
            Statement::VarReassign(id, val) => {
                let val = self.eval_expr(&val)?;
                if let None = self.env.reassign_var(&id, val) {
                    return Err(InterpreterError::raise(InterpreterErrorType::ValueError));
                }
            }
            Statement::TopLevelConstruct(construct) => match construct {
                TopLevelConstruct::Function(id, params, stmts) => {
                    self.env.insert_fn(id, Function::from(params, stmts));
                }
                TopLevelConstruct::Class(id, stmts) => unimplemented!(),
            }
            // !!!
            Statement::Return(e) => {
                if self.context != ExecCtxt::Function {
                    return Err(InterpreterError::raise(InterpreterErrorType::SyntaxError));
                }
                let ret_expr = self.eval_expr(&e)?;
                return Ok(ExecRes::Result(ret_expr));
            }
            Statement::While { condition, body } => {
                self.scope_push();
                while {
                    match self.eval_expr(&condition)? {
                        Literal::Bool(b) => b,
                        _ => return Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
                    }
                } {
                    for stmt in &body {
                        match self.execute_statement(stmt.clone())? {
                            ExecRes::Normal => (), // Continue if no special result
                            ExecRes::Result(r) => {
                                self.scope_pop();
                                return Ok(ExecRes::Result(r)); // Return if we encounter a return statement
                            }
                        }
                    }
                }
                self.scope_pop();
            }
            // !!!
            Statement::Empty => (),
            Statement::IfThenElse { condition, if_branch, else_branch } => {
                let condition = self.eval_expr(&condition)?;
                let set = match condition {
                    Literal::Bool(b) => {
                        if b {
                            if_branch
                        } else {
                            if let Some(branch) = else_branch {
                                branch
                            } else {
                                return Ok(ExecRes::Normal);
                            }
                        }
                    }

                    _ => return Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
                };
                self.scope_push();
                for stmt in set {
                    match self.execute_statement(stmt)? {
                        ExecRes::Normal => (),
                        ExecRes::Result(r) => { return Ok(ExecRes::Result(r)); }
                    }
                }
                self.scope_pop();
            }
        }
        Ok(ExecRes::Normal)
    }

    // TODO: remove clone calls
    pub fn run(&mut self) -> IResult<()> {
        let statements = self.statements.clone();
        self.exec_stmts(statements)
    }
}

// Show final snapshot of interpreter's state
impl Display for Interpreter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let contents = format!("Variable context:\n{:#?}\n\nStatements at beginning:\n{:#?}\n\nContext:{:#?}", self.env, self.statements, self.context);
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

    #[test]
    fn recursion() {
        let mut interpreter = Interpreter::new();
        let src = "
        fun hey(a, b) {
            if (a == 0) {
                return 1234;
            }
            var h = hey(0, 2);
            return h;
        }
        var b = hey(1, 2);";
        interpreter.init(src);
        interpreter.run().unwrap(); // Should not fail
    }
}