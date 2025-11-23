use std::{
    io::{BufRead, stdin},
    process::exit,
};

use anyhow::Result;
use randprog::random_program;

#[macro_use]
mod ast;
mod interpreter;
mod parser;
mod randprog;
mod tokeniser;

fn help() {
    eprintln!("minilisp - a tiny LISP interpreter.");
    eprintln!("Usage: minilisp [run FILE | repl | random | help] \n");
    eprintln!("Commands:");
    eprintln!("\t run [FILE]     --   Run a program at FILE.");
    eprintln!("\t                     If FILE is '-', the program will be read from stdin.\n");
    eprintln!("\t repl           --   Enter a primitive read-eval-print environment.");
    eprintln!("\t random         --   Generate a random minilisp program.");
    eprintln!("\t help           --   Print this message and exit.");
}

fn run(program: &str) -> Result<()> {
    let tokens = tokeniser::tokenise(program)?;

    let expression = parser::parse(tokens)?;

    let result = interpreter::interpret(expression)?;

    println!("{result}");

    Ok(())
}

fn repl() -> Result<String> {
    let mut program = String::new();
    stdin().lock().read_line(&mut program)?;
    println!("{:-<80}", "");
    Ok(program)
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

            if arg == "help" {
                help();
            } else if arg == "run" {
                let file = match args.next() {
                    None => {
                        eprintln!("The run command requires a file as an argument.");
                        help();
                        exit(1);
                    }
                    Some(file) => file,
                };

                if file == "-" {
                    run(args.collect::<String>().as_str())?;
                } else {
                    match std::fs::read_to_string(&file) {
                        Ok(program) => run(&program)?,
                        Err(err) => {
                            eprintln!("Failed to read program at {file}: {err}\n\n");
                            help();
                            exit(1);
                        }
                    }
                }
            } else if arg == "repl" {
                run(&repl()?)?;
            } else if arg == "random" {
                let program_expr = random_program()?;
                todo!("unparse and untokenise {program_expr:#?}");
            }
        }
    }

    Ok(())
}
