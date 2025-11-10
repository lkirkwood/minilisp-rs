use std::process::exit;

use anyhow::Result;

#[macro_use]
mod ast;
mod interpreter;
mod parser;
mod tokeniser;

fn help() {
    eprintln!("minilisp - a tiny LISP interpreter.");
    eprintln!("Usage: minilisp [--help | -h] [FILE]\n");
    eprintln!("If FILE is '-', the program will be read from stdin.\n");
    eprintln!("Options:");
    eprintln!("\t --help | -h    --   Print this message and exit.");
}

fn run(program: &str) -> Result<()> {
    let tokens = tokeniser::tokenise(program)?;

    let expression = parser::parse(tokens)?;

    let result = interpreter::interpret(expression)?;

    println!("{result}");

    Ok(())
}

fn main() -> Result<()> {
    let mut args = std::env::args();
    match args.nth(1) {
        None => {
            eprintln!("Error: a program to run is required as an argument.\n\n");
            help();
            exit(1);
        }
        Some(opt) if opt.as_str() == "-h" || opt.as_str() == "--help" => help(),
        Some(arg) if arg.as_str() == "-" => run(args.collect::<String>().as_str())?,
        Some(path) => match std::fs::read_to_string(&path) {
            Ok(program) => run(&program)?,
            Err(err) => {
                eprintln!("Failed to read program at {path}: {err}\n\n");
                help();
                exit(1);
            }
        },
    }

    Ok(())
}
