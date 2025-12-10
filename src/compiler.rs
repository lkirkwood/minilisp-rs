use std::collections::HashMap;

use anyhow::{Result, bail};

use crate::ast::{Expression, ParenExpression};
// NOTE previous attempt stashed

pub fn compile(program: Expression) -> Result<String> {
    let instructions = compile_expr(&mut Context::default(), program)?;

    Ok(format!(
        "global _start

section .text
_start:
{instructions}"
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
        Expression::Number(num) => Ok(format!("mov rax, {num}")),
        Expression::Identifier(ident) => {
            let Some(addr) = ctx.bindings.get(&ident) else {
                bail!("The program must be invalid, because \"{ident}\" is unbound.")
            };

            Ok(format!("mov rax, [{addr}]"))
        }
        Expression::Null => todo!("encoding for null"),
        Expression::Paren(parexpr) => compile_parexpr(ctx, *parexpr),
    }
}

fn compile_parexpr(ctx: &mut Context, parexpr: ParenExpression) -> Result<String> {
    match parexpr {
        ParenExpression::Plus { first, second } => Ok(format!(
            "{}
mov rbx, rax
{}
add rax, rbx",
            compile_expr(ctx, *first)?,
            compile_expr(ctx, *second)?
        )),
        other => todo!("compile other parexprs like {other:?}"),
    }
}
