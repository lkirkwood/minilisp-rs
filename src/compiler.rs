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

const TEMPLATE: &str = include_str!("compiler/template.asm");

/// Compile a program to NASM syntax `x86_64` instructions.
pub fn compile(program: Expression) -> Result<String> {
    Ok(TEMPLATE.to_string().replace(
        "    ; --- generated instructions ---\n",
        &compile_expr(&mut Context::default(), program)?,
    ))
}

#[derive(Default)]
/// Context the compiler needs to carry throughout the process.
struct Context {
    /// Identifiers mapped to an expression evaluating to the address storing the value.
    bindings: HashMap<String, Vec<String>>,
    /// Current offset from base pointer.
    current_offset: usize,
    /// Number of labels so far created.
    labels: usize,
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

    /// Create a new globally unique label.
    fn new_label(&mut self) -> String {
        let label = format!("label_{}", self.labels);
        self.labels += 1;
        label
    }
}

fn compile_expr(ctx: &mut Context, expr: Expression) -> Result<String> {
    match expr {
        Expression::Number(num) => {
            let num_addr = ctx.stack_allocate(8);
            Ok(join![
                cmd!("; store number: {}", num),
                cmd!("sub rsp, 8"),
                cmd!("mov qword {}, {}", num_addr, num),
                cmd!("lea retval, {}", num_addr),
                cmd!("or retval, num_t"),
                cmd!("; number stored")
            ])
        }
        Expression::Identifier(ident) => {
            let addr = ctx.get(&ident)?;
            Ok(join![
                cmd!("; return identifier {}", ident),
                // load address of value into rax
                cmd!("mov retval, {}", addr),
                cmd!("; {} returned", ident)
            ])
        }
        Expression::Null => Ok(join![cmd!("; emitting null"), cmd!("xor retval, retval")]),
        Expression::Paren(parexpr) => compile_parexpr(ctx, *parexpr),
    }
}

#[allow(clippy::similar_names)]
fn compile_parexpr(ctx: &mut Context, parexpr: ParenExpression) -> Result<String> {
    match parexpr {
        ParenExpression::Plus { first, second } => {
            let num_addr = ctx.stack_allocate(8);
            let first = compile_expr(ctx, *first)?;
            let second = compile_expr(ctx, *second)?;
            Ok(join![
                cmd!("; begin plus"),
                cmd!("sub rsp, 8"),
                cmd!("; compute first plus operand"),
                first,
                cmd!("; drop type info"),
                cmd!("and retval, bottom_3_zero"),
                cmd!("; store first plus operand"),
                cmd!("mov rax, [retval]"),
                cmd!("mov {}, rax", num_addr),
                cmd!("; compute second plus operand"),
                second,
                cmd!("; drop type info"),
                cmd!("and retval, bottom_3_zero"),
                cmd!("; perform plus operation"),
                cmd!("mov rax, [retval]"),
                cmd!("add {}, rax", num_addr),
                cmd!("jc generic_error"),
                cmd!("lea retval, {}", num_addr),
                cmd!("or retval, num_t"),
                cmd!("; end plus")
            ])
        }
        ParenExpression::Monus { first, second } => {
            let addr = ctx.stack_allocate(8);
            let calc_label = ctx.new_label();
            let end_label = ctx.new_label();
            let first = compile_expr(ctx, *first)?;
            let second = compile_expr(ctx, *second)?;
            Ok(join![
                cmd!("; begin monus"),
                cmd!("sub rsp, 8"),
                cmd!("; compute first monus operand"),
                first,
                cmd!("; drop type info"),
                cmd!("and retval, bottom_3_zero"),
                cmd!("; store first monus operand"),
                cmd!("mov rax, [retval]"),
                cmd!("mov {}, rax", addr),
                cmd!("; compute second monus operand"),
                second,
                cmd!("; drop type info"),
                cmd!("and retval, bottom_3_zero"),
                cmd!("; start calculation"),
                cmd!("mov rax, [retval]"),
                cmd!("cmp {}, rax", addr),
                cmd!("jg {}", calc_label),
                cmd!("mov {}, 0", addr),
                cmd!("jmp {}", end_label),
                cmd!("{}: ; perform calculation", calc_label),
                cmd!("sub {}, rax", addr),
                cmd!("{}: ; end of calculation", end_label),
                cmd!("lea retval, {}", addr),
                cmd!("or retval, num_t"),
                cmd!("; end monus")
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
                cmd!("lea retval, {}", car_addr),
                cmd!("and retval, bottom_3_zero"),
                cmd!("or retval, cons_t"),
                cmd!("; end cons")
            ])
        }
        ParenExpression::Car { cons } => Ok(join![
            compile_expr(ctx, *cons)?,
            cmd!("; get car from cons"),
            cmd!("and retval, bottom_3_zero"),
            cmd!("mov retval, [retval]"),
            cmd!("; end car")
        ]),
        ParenExpression::Cdr { cons } => Ok(join![
            compile_expr(ctx, *cons)?,
            cmd!("; get cdr from cons"),
            cmd!(";; get type info"),
            cmd!("mov rax, bottom_3_set"),
            cmd!("and rax, retval"),
            cmd!(";; drop type info for real pointer"),
            cmd!("and retval, bottom_3_zero"),
            cmd!("lea retval, [retval - 8]"),
            cmd!("mov retval, [retval]"),
            cmd!("or retval, rax"),
            cmd!("; end cdr")
        ]),
        ParenExpression::NullCheck { value } => {
            let value_code = compile_expr(ctx, *value)?;
            let num_addr = ctx.stack_allocate(8);
            let skip_label = ctx.new_label();
            Ok(join![
                value_code,
                cmd!("; start null check"),
                cmd!("sub rsp, 8"),
                cmd!("mov qword {}, 0", num_addr),
                cmd!("cmp retval, 0"),
                cmd!("jne {} ; value is not null, skip setting bool", skip_label),
                cmd!("mov qword {}, 1", num_addr),
                cmd!("{}:", skip_label),
                cmd!("lea retval, {}", num_addr)
            ])
        }
        other => todo!("compile other parexprs like {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, process::Command, u64};

    use crate::ast::{Expression, ParenExpression};

    use super::compile;

    fn write_asm_file(expr: Expression, filename: &str) {
        let asm = compile(expr.clone()).unwrap();
        fs::write(format!("asmtest/{filename}.asm"), asm).unwrap();

        let output = Command::new("bash")
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
    }

    fn run_asm_file(filename: &str, expected_status: i32, expected_output: Option<u64>) {
        let output = Command::new(format!("./asmtest/{filename}"))
            .output()
            .unwrap();
        dbg!(str::from_utf8(&output.stderr).unwrap());
        assert_eq!(output.status.code(), Some(expected_status));

        if let Some(expected_bytes) = expected_output {
            let mut actual_bytes_vec = output.stdout;
            while actual_bytes_vec.len() < 8 {
                actual_bytes_vec.push(0);
            }
            let mut actual_bytes = [0; 8];
            actual_bytes.copy_from_slice(&actual_bytes_vec);
            assert_eq!(u64::from_le_bytes(actual_bytes), expected_bytes);
        } else {
            assert!(output.stdout.is_empty());
        }
    }

    macro_rules! compile_test {
        ($name:ident, $expr:expr) => {
            #[test]
            fn $name() {
                let filename = stringify!($name);
                write_asm_file($expr, &filename);
                run_asm_file(&filename, 0, Some(42))
            }
        };

        ($name:ident, $expr:expr, $output:expr) => {
            #[test]
            fn $name() {
                let filename = stringify!($name);
                write_asm_file($expr, &filename);
                run_asm_file(&filename, 0, $output)
            }
        };

        ($name:ident, $expr:expr, $code:expr, $output:expr) => {
            #[test]
            fn $name() {
                let filename = stringify!($name);
                write_asm_file($expr, &filename);
                run_asm_file(&filename, $code, $output)
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

    // (+ INT_MAX 1)
    //
    // = overflow error
    compile_test!(
        compile_plus_overflow_error,
        Expression::Paren(Box::new(ParenExpression::Plus {
            first: Box::new(Expression::Number(u64::MAX)),
            second: Box::new(Expression::Number(1))
        })),
        1,
        None
    );

    // (+ INT_MAX 0)
    //
    // = INT_MAX
    compile_test!(
        compile_plus_overflow_almost,
        Expression::Paren(Box::new(ParenExpression::Plus {
            first: Box::new(Expression::Number(u64::MAX)),
            second: Box::new(Expression::Number(0))
        })),
        Some(u64::MAX)
    );

    // (− 43 1)
    //
    // = 42
    compile_test!(
        compile_monus,
        Expression::Paren(Box::new(ParenExpression::Monus {
            first: Box::new(Expression::Number(43)),
            second: Box::new(Expression::Number(1))
        }))
    );

    // (− 1 42)
    //
    // = 0
    compile_test!(
        compile_monus_saturates,
        Expression::Paren(Box::new(ParenExpression::Monus {
            first: Box::new(Expression::Number(1)),
            second: Box::new(Expression::Number(42))
        })),
        Some(0)
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

    compile_test!(
        compile_null_check,
        *boxparexpr!(ParenExpression::NullCheck {
            value: Box::new(Expression::Null)
        }),
        Some(1)
    );

    compile_test!(
        compile_null_check_on_number,
        *boxparexpr!(ParenExpression::NullCheck {
            value: Box::new(Expression::Number(1))
        }),
        Some(0)
    );

    // TODO test print cons
}
