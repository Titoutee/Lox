use std::fmt::Display;
use std::rc::Rc;

#[allow(unused)]
#[derive(Debug)]
pub struct InnerError {
    line: String,
    error_msg: String,
}

#[derive(Debug)]
pub enum InterpreterErrorType {
    SyntaxError,
    TypeError,
    ValueError,
    ArgumentCountError,
}

#[derive(Debug)]
pub struct InterpreterError {
    _type: Rc<InterpreterErrorType>,
    warning: String, // Built according to error _type
}

impl InterpreterError {
    pub fn raise(_type: InterpreterErrorType) -> Self {
        let _type = Rc::new(_type);
        InterpreterError {
            _type: Rc::clone(&_type),
            warning: warning(Rc::clone(&_type)),
        }
    }
}

impl Display for InterpreterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}\n{}", self._type, self.warning)
    }
}

// Matches errors to their respective warning messages, using context
fn warning(error_type: Rc<InterpreterErrorType>) -> String {
    match *error_type {
        InterpreterErrorType::ArgumentCountError => String::from("ArgumentCountError"),
        InterpreterErrorType::SyntaxError => String::from("SyntaxError"),
        InterpreterErrorType::TypeError => String::from("TypeError"),
        InterpreterErrorType::ValueError => String::from("ValueError"),
    }
    // TODO: add context
}

