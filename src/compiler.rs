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

const PRELUDE: &str = "
global _start

section .data
    ; byte holding current values type
    type: resb 1
    type_size: db 1,8,16,8,8

section .text
_start:
    ; syscalls
    %define sys_brk         12
    %define sys_write       1

    ; registers
    ;; pointer to the start of the available region of heap
    %define next_heap       r15
    ;; pointer to end of the heap
    %define heap_end        r14
    ;; pointer to the last returned value
    %define retval          r13

    ; other constants
    ;; page size (4KB)
    %define page            4096
    ;; value types that can occupy [type]
    %define null_t          0
    %define num_t           1
    %define cons_t          2
    %define lambda_t        3
    %define application_t   4

    jmp main

alloc_page:
    mov rax, sys_brk
    mov rdi, page
    add rdi, heap_end
    syscall
    ret

exit:
    mov rax, 60
    xor rdi, rdi
    syscall

main:
    %macro error 1
        mov rdi, %1
        jmp exit
    %endmacro

    ; set base pointer to current stack location
    mov rbp, rsp

    ; generated instructions
";

const PRINT_RAX_AND_EXIT: &str = "

    ; print result and exiting


    ; set length of output by type
    xor rdx, rdx
    mov byte dl, [type]
    mov rdi, type_size
    mov byte dl, [rdi + rdx]

    mov rsi, retval
    mov rax, sys_write
    ; set fd to 1 (stdout)
    mov rdi, 1
    syscall

    xor rdi, rdi
    jmp exit
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
        let _ = self.stack_allocate(1); // for type byte
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
                cmd!("sub rsp, 8"),
                cmd!("mov qword {}, {}", addr, num),
                cmd!("lea retval, {}", addr),
                cmd!("mov byte [type], num_t"),
                cmd!("; number stored")
            ])
        }
        Expression::Identifier(ident) => {
            let addr = ctx.get(&ident)?;
            Ok(join![
                cmd!("; return identifier {}", ident),
                // load address of value into rax
                cmd!("mov retval, {}", addr),
                cmd!("lea rax, {}", addr),
                cmd!("sub rax, 1"),
                cmd!("mov byte al, [rax]"),
                cmd!("mov byte [type], al"), // 1 byte version of rax
                cmd!("; {} returned", ident)
            ])
        }
        Expression::Null => Ok(join![
            cmd!("; emitting null"),
            cmd!("xor retval, retval"),
            cmd!("mov byte [type], null_t")
        ]),
        Expression::Paren(parexpr) => compile_parexpr(ctx, *parexpr),
    }
}

fn compile_parexpr(ctx: &mut Context, parexpr: ParenExpression) -> Result<String> {
    match parexpr {
        ParenExpression::Plus { first, second } => {
            let addr = ctx.stack_allocate(8);
            let first = compile_expr(ctx, *first)?;
            let second = compile_expr(ctx, *second)?;
            Ok(join![
                cmd!("; begin plus"),
                cmd!("sub rsp, 8"),
                cmd!("; compute first plus operand"),
                first,
                cmd!("; store first plus operand"),
                cmd!("mov rax, [retval]"),
                cmd!("mov {}, rax", addr),
                cmd!("; compute second plus operand"),
                second,
                cmd!("; perform plus operation"),
                cmd!("mov rax, [retval]"),
                cmd!("add {}, rax", addr),
                cmd!("lea retval, {}", addr),
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
                cmd!("sub rsp, 9"),
                cmd!("mov {}, retval", addr),
                cmd!("lea rax, {}", addr),
                cmd!("mov byte dl, [type]"),
                cmd!("mov byte [rax - 1], dl"),
                cmd!("; binding body start"),
                body_code,
                cmd!("; unbind {}", name)
            ])
        }
        ParenExpression::Cons { car, cdr } => {
            let car_addr = ctx.stack_allocate(8);
            let cdr_addr = ctx.stack_allocate(8);
            let car_code = compile_expr(ctx, *car)?;
            let cdr_code = compile_expr(ctx, *cdr)?;
            Ok(join![
                cmd!("; start cons"),
                cmd!("sub rsp, 16"),
                cmd!("; compute car"),
                car_code,
                cmd!("mov {}, retval", car_addr),
                cmd!("; stored car, compute cdr"),
                cdr_code,
                cmd!("mov {}, retval", cdr_addr),
                cmd!("; stored cdr, return car address"),
                cmd!("mov retval, {}", car_addr),
                cmd!("; end cons")
            ])
        }
        ParenExpression::Car { cons } => Ok(join![
            compile_expr(ctx, *cons)?,
            cmd!("; get car from cons"),
            cmd!("; noop - retval already points to start of cons"),
            cmd!("; end car")
        ]),
        ParenExpression::Cdr { cons } => Ok(join![
            compile_expr(ctx, *cons)?,
            cmd!("; get cdr from cons"),
            cmd!("lea retval, [retval - 8]"),
            cmd!("; end cdr")
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

    // (≜ foo (∷ 42 99)
    //     (← foo))
    //
    // = 42
    compile_test!(
        compile_cons_car,
        *boxparexpr!(ParenExpression::Binding {
            name: "foo".to_string(),
            value: boxparexpr!(ParenExpression::Cons {
                car: Box::new(Expression::Number(42)),
                cdr: Box::new(Expression::Number(99))
            }),
            body: boxparexpr!(ParenExpression::Car {
                cons: Box::new(Expression::Identifier("foo".to_string()))
            })
        })
    );

    // (≜ foo (∷ 99 42)
    //     (→ foo))
    //
    // = 42
    compile_test!(
        compile_cons_cdr,
        *boxparexpr!(ParenExpression::Binding {
            name: "foo".to_string(),
            value: boxparexpr!(ParenExpression::Cons {
                car: Box::new(Expression::Number(99)),
                cdr: Box::new(Expression::Number(42))
            }),
            body: boxparexpr!(ParenExpression::Cdr {
                cons: Box::new(Expression::Identifier("foo".to_string()))
            })
        })
    );
}
