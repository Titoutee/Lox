use lox::Interpreter;
use std::env;
use std::fs;
use std::io::{self, Write};

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut stderr_handle = io::stderr();

    if args.len() < 2 {
        writeln!(stderr_handle, "Usage: {} tokenize <filename>", args[0]).unwrap();
        return;
    }

    let filename: &String = &args[1];
    let contents = fs::read_to_string(filename).unwrap();

    let mut interpreter = Interpreter::new();
    interpreter.init(&contents);
    match interpreter.run() {
        Err(err) => eprintln!("Intepreter failed to run: {}", err),
        _ => println!("{}", interpreter),
    };
}
