use std::{
    io::{BufRead, stdin},
    process::exit,
};

use anyhow::Result;

#[macro_use]
mod ast;
mod interpreter;
mod parser;
mod tokeniser;

fn help() {
    eprintln!("minilisp - a tiny LISP interpreter.");
    eprintln!("Usage: minilisp [--help | -h] [--repl | -r] [FILE]\n");
    eprintln!("If FILE is '-', the program will be read from stdin.\n");
    eprintln!("Options:");
    eprintln!("\t --help | -h    --   Print this message and exit.");
    eprintln!("\t --repl | -r    --   Enter a primitive REPL.");
}

fn repl() -> Result<String> {
    let mut program = String::new();
    stdin().lock().read_line(&mut program)?;
    println!("{:-<80}", "");
    Ok(program)
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
            eprintln!("Error: at least one argument is required.\n\n");
            help();
            exit(1);
        }
        Some(arg) => {
            let arg = arg.as_str();

            if matches!(arg, "--help" | "-h") {
                help();
            } else if matches!(arg, "--repl" | "-r") {
                run(&repl()?)?;
            } else if arg == "-" {
                run(args.collect::<String>().as_str())?;
            } else {
                match std::fs::read_to_string(arg) {
                    Ok(program) => run(&program)?,
                    Err(err) => {
                        eprintln!("Failed to read program at {arg}: {err}\n\n");
                        help();
                        exit(1);
                    }
                }
            }
        }
    }

    Ok(())
}
