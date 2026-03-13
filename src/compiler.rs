use std::collections::{HashMap, hash_map::Entry};

use anyhow::{Result, bail};

use crate::ast::{Expression, ParenExpression};

/// Format a string literal using format!,
/// wrapping it in 4 leading spaces and a trailing newline.
macro_rules! cmd {
    ($cmd:expr $(, $arg:expr)*) => {
        format!(concat!("    ", $cmd, "\n") $(, $arg)*)
    };
}

/// Join some strings with no separator.
macro_rules! join {
    ($first:expr $(, $others:expr)*) => {
        vec![$first $(, $others)*].into_iter().collect::<String>()
    }
}

/// The types that a value can take.
enum Type {
    NULL = 0,
    INT = 1,
    CONS = 2,
    LAMBDA = 3,
    APPLICATION = 4,
}

const PRELUDE: &str = "
global _start

section .text
_start:
    ; syscalls
    %define sys_brk     12
    %define sys_write   1

    ; registers

    ;; pointer to the start of the available region of heap
    %define next_heap   r15

    ;; pointer to end of the heap
    %define heap_end    r14

    ;; pointer to the last returned value
    %define retval      r13

    ; other constants
    %define page        4096

    jmp main

alloc_page:
    mov rax, sys_brk
    mov rdi, page
    add rdi, heap_end
    syscall
    ret

main:
    ; Ensure that there is at least %1 bytes left in the heap
    %macro ensuremem 1
        mov rax, %1
        add rax, next_heap          ; rax now has address of the end of new allocation

        cmp next_heap, heap_end
        jl alloc_page
    %endmacro

    ; set base pointer to current stack location
    mov rbp, rsp

    ; allocate 1kb
    ensuremem 1024

    ; generated instructions
";

const PRINT_RAX_AND_EXIT: &str = "

    ; printing result and exiting

    mov rsi, retval
    mov rax, sys_write
    ; set fd to 1 (stdout)
    mov rdi, 1
    ; set length to 1 byte TODO make this type dependent
    mov rdx, 1
    syscall

    ; exit
    mov rax, 60
    xor rdi, rdi
    syscall
";

/// Compile a program to NASM syntax x86_64 instructions.
pub fn compile(program: Expression) -> Result<String> {
    let instructions = compile_expr(&mut Context::default(), program)?;

    Ok(join!(PRELUDE, &instructions, PRINT_RAX_AND_EXIT))
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
    /// Allocate `num_bytes` and return their location in memory.
    fn stack_allocate(&mut self, num_bytes: usize) -> String {
        self.current_offset += num_bytes;
        format!("[rbp - {}]", self.current_offset)
    }

    /// Allocate 8 bytes on the stack and bind `ident` to them.
    /// Return their location in memory.
    fn bind(&mut self, ident: String) -> String {
        let addr = self.stack_allocate(8);
        match self.bindings.entry(ident) {
            Entry::Occupied(mut entry) => entry.get_mut().push(addr.clone()),
            Entry::Vacant(entry) => {
                entry.insert(vec![addr.clone()]);
            }
        }
        addr
    }

    /// Unbind the innermost binding for `ident`.
    fn unbind(&mut self, ident: &str) -> Result<()> {
        if let Some(addrs) = self.bindings.get_mut(ident)
            && !addrs.is_empty()
        {
            addrs.pop();
            return Ok(());
        }
        bail!("Tried to unbind unbound identifier {ident}")
    }

    /// Get the offset address `ident` is bound to.
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
        Expression::Number(num) => {
            let addr = ctx.stack_allocate(8);
            Ok(join![
                cmd!("; store number: {}", num),
                cmd!("mov qword {}, {}", addr, num),
                cmd!("lea retval, {}", addr),
                cmd!("; number stored")
            ])
        }
        Expression::Identifier(ident) => Ok(join![
            cmd!("; return identifier {}", ident),
            // load address of value into rax
            cmd!("mov retval, {}", ctx.get(&ident)?),
            cmd!("; {} returned", ident)
        ]),
        Expression::Null => todo!("encoding for null"),
        Expression::Paren(parexpr) => compile_parexpr(ctx, *parexpr),
    }
}

fn compile_parexpr(ctx: &mut Context, parexpr: ParenExpression) -> Result<String> {
    match parexpr {
        ParenExpression::Plus { first, second } => {
            let first = compile_expr(ctx, *first)?;
            let second = compile_expr(ctx, *second)?;
            let addr = ctx.stack_allocate(8);
            Ok(join![
                cmd!("; begin plus"),
                first,
                cmd!("mov {}, retval", addr),
                second,
                cmd!("mov rdi, {}", addr),
                cmd!("mov rax, [rdi]"),
                cmd!("add rax, [retval]"),
                cmd!("mov {}, rax", addr),
                cmd!("mov retval, {}", addr),
                cmd!("; end plus")
            ])
        }
        ParenExpression::Binding { name, value, body } => {
            let value_code = compile_expr(ctx, *value)?;
            // Offset address of a pointer to the value computed above.
            let addr = ctx.bind(name.clone());
            let body_code = compile_expr(ctx, *body)?;
            ctx.unbind(&name)?;
            Ok(join![
                cmd!("; bind {}", name),
                value_code,
                cmd!("; store computed value of {}", name),
                cmd!("sub rsp, 8"),
                cmd!("mov {}, retval", addr),
                cmd!("; binding body start"),
                body_code,
                cmd!("; unbind {}", name)
            ])
        }
        ParenExpression::Cons { car, cdr } => Ok(join![
            cmd!("; start cons"),
            cmd!("ensuremem 128"),
            cmd!(""),
            cmd!("; end cons")
        ]),
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
                    "nasm -f elf64 -g -F dwarf asmtest/{filename}.asm -o asmtest/{filename}.o && \
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
        dbg!(str::from_utf8(&output.stderr).unwrap());
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, vec![42]);

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
