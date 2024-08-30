use std::sync::{Arc, OnceLock};
use crate::common::error::{InterpreterError, InterpreterErrorType};
use crate::parsing::Literal;
use crate::IResult;

pub type FnPtr = Arc<dyn Fn(Vec<Literal>) -> IResult<Literal> + Sync + Send>;

pub struct Routine {
    pub ptr: FnPtr,
}

impl Routine {    
    pub fn call(&self, args: Vec<Literal>) -> IResult<Literal> {
        (self.ptr)(args)
    }
}

pub static BUILT_INS: OnceLock<Vec<(&'static str, FnPtr)>> = OnceLock::new();

// This function contains the routine definitions of the entire stdlib.
// It may be split when the latter grows.
pub fn initialize_built_ins() -> Vec<(&'static str, FnPtr)> {
    vec![
        // Output
        ("print", Arc::new(|args: Vec<Literal>| {
            for a in args {
                print!("{}", a);
            }
            Ok(Literal::Nil)
        })),

        ("printline", Arc::new(|args: Vec<Literal>| {
            for a in args {
                print!("{}", a);
            }
            println!();
            Ok(Literal::Nil)
        })),

        // String ops
        ("strlen", Arc::new(|args: Vec<Literal>| {
            let arg = if let Some(v) = args.get(0) { v } else { return Err(InterpreterError::raise(InterpreterErrorType::ArgumentCountError))};
            match arg {
                Literal::String(s) => Ok(Literal::Number(s.len() as f64)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
        })),
    ]
}