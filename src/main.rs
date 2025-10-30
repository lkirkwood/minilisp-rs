use anyhow::{bail, Result};

mod model;
mod tokeniser;

fn main() -> Result<()> {
    let mut args = std::env::args();
    match args.next() {
        None => bail!("Path to a program required as an argument."),
        Some(path) => match std::fs::read_to_string(&path) {
            Ok(program_string) => {
                let tokens = tokeniser::tokenise(&program_string)?;
                dbg!(tokens);
                println!("Tokenised OK!");
            }
            Err(err) => bail!("Failed to read program at {path}: {err}"),
        },
    }

    Ok(())
}
