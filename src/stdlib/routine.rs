use std::sync::{Arc, OnceLock};
use crate::common::error::{InterpreterError, InterpreterErrorType};
use crate::parsing::Literal;
use crate::IResult;

/// A function pointer is any `Fn` closure taking a list of parameters and returning a `Literal`
/// wrapped in `IResult`.
/// `FnPtr` is thread-safe because wrapped in thread-safe `OnceLock`.
pub type FnPtr = Arc<dyn Fn(Vec<Literal>) -> IResult<Literal> + Sync + Send>;

/// A routine as a pointer to a dynamically-compiled std function.
pub struct Routine {
    pub ptr: FnPtr,
}

impl Routine {
    // Thin wrapper aroud a simple fp dereferencing procedure.
    pub fn call(&self, args: Vec<Literal>) -> IResult<Literal> {
        (self.ptr)(args)
    }
}

/// List of built-in std routines, empty at declaration.
pub static BUILT_INS: OnceLock<Vec<(&'static str, FnPtr)>> = OnceLock::new();

// This function defines the routine for the entire Lox stdlib.
// This may evolve to a cleaner implementation later on.
/// A routine for dynamic routine definition.
pub fn initialize_built_ins() -> Vec<(&'static str, FnPtr)> {
    vec![
        // ~ I/O ~
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

        // ~ String ops ~
        ("strlen", Arc::new(|args: Vec<Literal>| {
            let arg = if let Some(v) = args.get(0) { v } else { return Err(InterpreterError::raise(InterpreterErrorType::ArgumentCountError))};
            match arg {
                Literal::String(s) => Ok(Literal::Number(s.len() as f64)),
                _ => Err(InterpreterError::raise(InterpreterErrorType::TypeError)),
            }
        })),
    ]
}