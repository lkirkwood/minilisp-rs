use std::{
    env::Args,
    io::{BufRead, Read, stdin},
    process::exit,
};

use anyhow::Result;
use compiler::compile;
use randprog::random_program;

#[macro_use]
mod ast;
mod compiler;
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
    eprintln!("\t compile        --   Compile a minilisp program to x86 assembly.");
    eprintln!("\t help           --   Print this message and exit.");
}

fn read_file(mut args: Args) -> Result<String> {
    let Some(file) = args.next() else {
        eprintln!("The run command requires a file as an argument.");
        help();
        exit(1);
    };

    if file == "-" {
        let mut buf = Vec::new();
        stdin().lock().read_to_end(&mut buf)?;
        Ok(String::from_utf8(buf)?)
    } else {
        match std::fs::read_to_string(&file) {
            Ok(program) => Ok(program),
            Err(err) => {
                eprintln!("Failed to read program at {file}: {err}\n\n");
                help();
                exit(1);
            }
        }
    }
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
            } else if arg == "repl" {
                run(&repl()?)?;
            } else if arg == "random" {
                println!("{}", random_program());
            } else if arg == "compile" {
                let program = read_file(args)?;
                let tokens = tokeniser::tokenise(&program)?;
                let expression = parser::parse(tokens)?;
                println!("{}", compile(expression));
            } else {
                eprintln!("Unrecognised command: {arg}.");
                help();
                exit(1);
            }
        }
    }

    Ok(())
}
