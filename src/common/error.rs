use std::fmt::Display;

pub struct SyntaxError {

}

pub struct TypeError {
    
}

#[derive(Debug)]
pub enum InterpreterErrorType {
    SyntaxError,
    TypeError,
    ValueError,
}

#[derive(Debug)]
pub struct InterpreterError<'a> {
    _type: &'a InterpreterErrorType,
    warning: String, // Built according to error _type
}

impl<'a> InterpreterError<'a> {
    pub fn raise(_type: &'a InterpreterErrorType) -> Self {
        InterpreterError {
            _type,
            warning: warning(_type),
        }
    }
}

impl<'a> Display for InterpreterError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}\n{}", self._type, self.warning)
    }
}

// Matches errors to their respective warning messages, using context
fn warning(error_type: &InterpreterErrorType) -> String {
    match *error_type {
        InterpreterErrorType::SyntaxError => String::from("Syntax error"),
        InterpreterErrorType::TypeError => String::from("Type error"),
        InterpreterErrorType::ValueError => String::from("Value error"),
    }
    // TODO: add context
}

