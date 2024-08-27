use lox::Interpreter;
use std::{fs, process::exit};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[clap(short, long)]
    file: String,

    #[clap(short, long, action)]
    context: bool,
}

fn main() {
    let args = Args::parse();

    let contents = if let Ok(s) = fs::read_to_string(args.file) {s} else {
        eprintln!("File not found!");
        exit(1);
    };

    let mut interpreter = Interpreter::new();
    interpreter.init(&contents);

    match interpreter.run() {
        Err(err) => eprintln!("Intepreter failed to run: {}", err),
        _ => {
            if args.context {
                println!("{}", interpreter)
            }
        }
    };
}