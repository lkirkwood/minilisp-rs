use std::collections::{HashMap, hash_map::Entry};

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

    mov rbp, rsp

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
    /// Identifiers mapped to an expression evaluating to the address storing the value.
    bindings: HashMap<String, Vec<String>>,
    /// Current offset from base pointer.
    current_offset: usize,
}

impl Context {
    fn bind(&mut self, ident: String) -> String {
        self.current_offset += 8;
        let value = format!("[rbp - {}]", self.current_offset);
        match self.bindings.entry(ident) {
            Entry::Occupied(mut entry) => entry.get_mut().push(value.clone()),
            Entry::Vacant(entry) => {
                entry.insert(vec![value.clone()]);
            }
        }
        value
    }

    fn get(&mut self, ident: &str) -> Result<String> {
        if let Some(addrs) = self.bindings.get(ident)
            && !addrs.is_empty()
        {
            return Ok(addrs.last().unwrap().clone());
        }
        bail!("Tried to use an unbound identifier: {ident}");
    }
}

fn compile_expr(ctx: &mut Context, expr: Expression) -> Result<String> {
    match expr {
        Expression::Number(num) => Ok(format!("    mov rax, {num}")),
        Expression::Identifier(ident) => Ok(format!("    mov rax, {}", ctx.get(&ident)?)),
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
        // Need to know the address where the value will be stored so that
        // we can map ident to that address. Problem is we can't reserve memory
        // upfront because we don't know the size of the value until it is
        // computed at runtime. So we have to emit ASM that will store the
        // address of the value in a variable of the same name as the ident.
        //
        // To do this probably have to emit some runtime type information.
        // Can elect a register to always contain a byte indicating the type of
        // value.
        ParenExpression::Binding { name, value, body } => {
            let value_code = compile_expr(ctx, *value)?;
            let addr = ctx.bind(name);
            let body_code = compile_expr(ctx, *body)?;
            Ok(format!("{value_code}\n\tmov {addr}, rax\n{body_code}"))
        }
        other => todo!("compile other parexprs like {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, process::Command};

    use crate::ast::{Expression, ParenExpression};

    use super::compile;

    fn write_asm_file(expr: Expression, filename: &str) {
        let asm = compile(expr.clone()).unwrap();
        fs::write(format!("asmtest/{filename}.asm"), asm).unwrap();

        let mut output = Command::new("bash")
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
        assert_eq!(output.status.code(), Some(0));

        output = Command::new(format!("./asmtest/{filename}"))
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(0));

        // TODO compare output to interpreter
    }

    macro_rules! compile_test {
        ($name:ident, $expr:expr) => {
            #[test]
            fn $name() {
                write_asm_file($expr, &stringify!($name));
            }
        };
    }

    //// Actual tests ////

    // 42
    //
    // = 42
    compile_test!(compile_num, Expression::Number(42));

    // (+ 41 1)
    //
    // = 42
    compile_test!(
        compile_plus,
        Expression::Paren(Box::new(ParenExpression::Plus {
            first: Box::new(Expression::Number(41)),
            second: Box::new(Expression::Number(1))
        }))
    );

    // (≜ foo 42 foo)
    //
    // = 42
    compile_test!(
        compile_ident,
        *boxparexpr!(ParenExpression::Binding {
            name: "foo".to_string(),
            value: Box::new(Expression::Number(42)),
            body: Box::new(Expression::Identifier("foo".to_string()))
        })
    );

    // (≜ foo 41
    //     (≜ bar 1
    //         (+ foo bar)))
    //
    // = 42
    compile_test!(
        compile_ident_plus,
        *boxparexpr!(ParenExpression::Binding {
            name: "foo".to_string(),
            value: Box::new(Expression::Number(41)),
            body: boxparexpr!(ParenExpression::Binding {
                name: "bar".to_string(),
                value: Box::new(Expression::Number(1)),
                body: boxparexpr!(ParenExpression::Plus {
                    first: Box::new(Expression::Identifier("foo".to_string())),
                    second: Box::new(Expression::Identifier("bar".to_string()))
                })
            })
        })
    );
}
