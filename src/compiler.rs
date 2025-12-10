use std::collections::HashMap;

use anyhow::{Result, bail};

use crate::ast::{Expression, ParenExpression};
// NOTE previous attempt stashed

pub fn compile(program: Expression) -> Result<String> {
    let instructions = compile_expr(&mut Context::default(), program)?;

    Ok(format!(
        "global _start

section .bss
    output resb 8

section .text
_start:

    ;; generated instructions
{instructions}

    ;; printing result and exiting
    mov [output], rax
    mov rax, 1
    mov rdi, 1
    mov rsi, output
    mov rdx, 8
    syscall

    mov rax, 60
    xor rdi, rdi
    syscall"
    ))
}

#[derive(Default)]
/// Context the compiler needs to carry throughout the process.
struct Context {
    /// List of identifiers and the address their value is stored at.
    bindings: HashMap<String, usize>,
}

fn compile_expr(ctx: &mut Context, expr: Expression) -> Result<String> {
    match expr {
        Expression::Number(num) => Ok(format!("    mov rax, {num}")),
        Expression::Identifier(ident) => {
            let Some(addr) = ctx.bindings.get(&ident) else {
                bail!("The program must be invalid, because \"{ident}\" is unbound.")
            };

            Ok(format!("    mov rax, [{addr}]"))
        }
        Expression::Null => todo!("encoding for null"),
        Expression::Paren(parexpr) => compile_parexpr(ctx, *parexpr),
    }
}

fn compile_parexpr(ctx: &mut Context, parexpr: ParenExpression) -> Result<String> {
    match parexpr {
        ParenExpression::Plus { first, second } => Ok(format!(
            "\
{}
    mov rbx, rax
{}
    add rax, rbx",
            compile_expr(ctx, *first)?,
            compile_expr(ctx, *second)?
        )),
        other => todo!("compile other parexprs like {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, process::Command};

    use crate::ast::{Expression, ParenExpression};

    use super::compile;

    fn write_asm_file(asm: &str, filename: &str) {
        fs::write(format!("asmtest/{filename}.asm"), asm).unwrap();

        let output = Command::new("bash")
            .args([
                "-c",
                &format!(
                    "nasm -f elf64 -g asmtest/{filename}.asm -o asmtest/{filename}.o && \
                    ld -o asmtest/{filename} asmtest/{filename}.o"
                ),
            ])
            .output()
            .unwrap();

        eprintln!("{}", str::from_utf8(&output.stderr).unwrap());
        assert_eq!(output.status.code().unwrap(), 0);
    }

    macro_rules! compile_test {
        ($name:ident, $expr:expr) => {
            #[test]
            fn $name() {
                write_asm_file(&compile($expr).unwrap(), &stringify!($name));
            }
        };
    }

    compile_test!(compile_num, Expression::Number(42));

    compile_test!(
        compile_plus,
        Expression::Paren(Box::new(ParenExpression::Plus {
            first: Box::new(Expression::Number(42)),
            second: Box::new(Expression::Number(1))
        }))
    );
}
