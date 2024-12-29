use lox::Interpreter;
use std::fs;
use clap::Parser;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// The file to be interpreted
    #[clap(short, long)]
    file: String,

    /// Whether final context should be displayed (verbose mode)
    #[clap(short, long, action)]
    context: bool,
}

fn main() {
    let args = Args::parse();

    let contents = if let Ok(s) = fs::read_to_string(args.file) {s} else {
        eprintln!("File not found!");
        panic!();
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