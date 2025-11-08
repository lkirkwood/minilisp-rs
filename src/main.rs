use anyhow::{Result, bail};

#[macro_use]
mod ast;
mod interpreter;
mod parser;
mod tokeniser;

fn main() -> Result<()> {
    let mut args = std::env::args();
    match args.nth(1) {
        None => bail!("Path to a program required as an argument."),
        Some(path) => match std::fs::read_to_string(&path) {
            Ok(program_string) => {
                let tokens = tokeniser::tokenise(&program_string)?;

                let expression = parser::parse(tokens)?;

                let result = interpreter::interpret(expression)?;

                println!("{result}");
            }
            Err(err) => bail!("Failed to read program at {path}: {err}"),
        },
    }

    Ok(())
}
