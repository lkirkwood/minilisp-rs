mod context;
mod lambda;

use anyhow::Result;
use lambda::{compile_application, compile_lambda};

use crate::ast::{Expression, ParenExpression};
use context::Context;

#[macro_export]
/// Format a string literal using format!,
/// wrapping it in 4 leading spaces and a trailing newline.
macro_rules! cmd {
    ($cmd:expr $(, $arg:expr)*) => {
        format!(concat!("    ", $cmd, "\n") $(, $arg)*)
    };
}

#[macro_export]
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

fn compile_expr(ctx: &mut Context, expr: Expression) -> Result<String> {
    match expr {
        Expression::Number(num) => Ok(join![
            cmd!("; store number: {}", num),
            cmd!("mov retval, {}", num),
            cmd!("mov rettype, qword num_t"),
            cmd!("; number stored")
        ]),
        Expression::Identifier(ident) => {
            let addr = ctx.get(&ident)?;
            Ok(join![
                cmd!("; return identifier {}", ident),
                cmd!("lea rdi, {}", addr),
                cmd!("mov retval, [rdi]"),
                cmd!("mov rettype, [rdi - 8]"),
                cmd!("; {} returned", ident)
            ])
        }
        Expression::Null => Ok(join![
            cmd!("; emitting null"),
            cmd!("xor retval, retval"),
            cmd!("xor rettype, rettype")
        ]),
        Expression::Paren(parexpr) => compile_parexpr(ctx, *parexpr),
    }
}

#[allow(clippy::similar_names)]
fn compile_parexpr(ctx: &mut Context, parexpr: ParenExpression) -> Result<String> {
    match parexpr {
        ParenExpression::Plus { first, second } => {
            let first = compile_expr(ctx, *first)?;
            let second = compile_expr(ctx, *second)?;
            Ok(join![
                cmd!("; begin plus"),
                cmd!("; compute first plus operand"),
                first,
                cmd!("; store first plus operand"),
                cmd!("mov [tmp_val], retval"),
                cmd!("; compute second plus operand"),
                second,
                cmd!("add retval, [tmp_val]"),
                cmd!("jc generic_error"),
                cmd!("; end plus")
            ])
        }
        ParenExpression::Monus { first, second } => {
            let calc_label = ctx.new_label();
            let end_label = ctx.new_label();
            let second = compile_expr(ctx, *second)?;
            let first = compile_expr(ctx, *first)?;
            Ok(join![
                cmd!("; begin monus"),
                cmd!("; compute second monus operand first"),
                second,
                cmd!("; store second monus operand"),
                cmd!("mov [tmp_val], retval"),
                cmd!("; compute first monus operand now"),
                first,
                cmd!("cmp retval, [tmp_val]"),
                cmd!("jg {}", calc_label),
                cmd!("xor retval, retval"),
                cmd!("jmp {}", end_label),
                cmd!("{}: ; perform calculation", calc_label),
                cmd!("sub retval, [tmp_val]"),
                cmd!("{}: ; end of calculation", end_label),
                cmd!("; end monus")
            ])
        }
        ParenExpression::Times { first, second } => {
            let first = compile_expr(ctx, *first)?;
            let second = compile_expr(ctx, *second)?;
            Ok(join![
                cmd!("; begin times"),
                cmd!("; compute first times operand"),
                first,
                cmd!("; store first times operand"),
                cmd!("mov [tmp_val], retval"),
                cmd!("; compute second times operand"),
                second,
                cmd!("mov rax, [tmp_val]"),
                cmd!("mul retval"),
                cmd!("mov retval, rax"),
                cmd!("jc generic_error"),
                cmd!("; end times")
            ])
        }
        ParenExpression::Binding { name, value, body } => {
            let value_code = compile_expr(ctx, *value)?;
            let _val_addr = ctx.stack_bind(name.clone());
            let _type_addr = ctx.stack_alloc(16);
            let body_code = compile_expr(ctx, *body)?;
            ctx.stack_free(16);
            ctx.unbind(&name)?;
            Ok(join![
                cmd!("; start binding"),
                cmd!("; bind {}", name),
                value_code,
                cmd!("; store computed value of {}", name),
                cmd!("push retval"),
                cmd!("push rettype"),
                cmd!("; binding body start"),
                body_code,
                cmd!("; unbind {}", name),
                cmd!("pop rax"),
                cmd!("pop rax"),
                cmd!("; end binding")
            ])
        }
        ParenExpression::Cons { car, cdr } => {
            let _heap_start = ctx.stack_alloc(8);
            let car_code = compile_expr(ctx, *car)?;
            let cdr_code = compile_expr(ctx, *cdr)?;
            ctx.stack_free(8);
            Ok(join![
                cmd!("; start cons"),
                cmd!("; allocate heap space"),
                cmd!("mov rdx, 32"),
                cmd!("call ensure_mem"),
                cmd!("push heap_start"),
                cmd!("add heap_start, 32"),
                cmd!("; compute car"),
                car_code,
                cmd!("; store car on heap"),
                cmd!("pop rdi"),
                cmd!("mov [rdi], retval"),
                cmd!("add rdi, 8"),
                cmd!("mov [rdi], rettype"),
                cmd!("add rdi, 8"),
                cmd!("push rdi"),
                cmd!("; stored car, compute cdr"),
                cdr_code,
                cmd!("; store cdr"),
                cmd!("pop rdi"),
                cmd!("mov [rdi], retval"),
                cmd!("add rdi, 8"),
                cmd!("mov [rdi], rettype"),
                cmd!("add rdi, 8"),
                cmd!("; stored cdr, return car address"),
                cmd!("mov retval, rdi"),
                cmd!("sub retval, 32"),
                cmd!("mov rettype, qword cons_t"),
                cmd!("; end cons")
            ])
        }
        ParenExpression::Car { cons } => Ok(join![
            compile_expr(ctx, *cons)?,
            cmd!("; get car from cons"),
            cmd!("mov rdi, retval"),
            cmd!("add rdi, 8"),
            cmd!("mov retval, [retval]"),
            cmd!("mov rettype, [rdi]"),
            cmd!("; end car")
        ]),
        ParenExpression::Cdr { cons } => Ok(join![
            compile_expr(ctx, *cons)?,
            cmd!("; get cdr from cons"),
            cmd!("add retval, 16"),
            cmd!("mov rdi, retval"),
            cmd!("add rdi, 8"),
            cmd!("mov retval, [retval]"),
            cmd!("mov rettype, [rdi]"),
            cmd!("; end cdr")
        ]),
        ParenExpression::NullCheck { value } => {
            let value_code = compile_expr(ctx, *value)?;
            let skip_label = ctx.new_label();
            Ok(join![
                value_code,
                cmd!("; start null check"),
                cmd!("cmp retval, 0"),
                cmd!("xor retval, retval"),
                cmd!("jne {} ; value is not null, skip setting bool", skip_label),
                cmd!("cmp rettype, 0"),
                cmd!("jne {} ; type is not null, skip setting bool", skip_label),
                cmd!("mov retval, 1"),
                cmd!("{}:", skip_label),
                cmd!("mov rettype, qword num_t")
            ])
        }
        ParenExpression::Lambda { arg, body } => compile_lambda(ctx, arg, body),
        ParenExpression::Application { lambda, argument } => {
            compile_application(ctx, *lambda, *argument)
        }
        ParenExpression::Condition { predicate, yes, no } => {
            let yes_label = ctx.new_label();
            let no_label = ctx.new_label();
            let finish_label = ctx.new_label();
            Ok(join![
                cmd!("; start conditional"),
                compile_expr(ctx, *predicate)?,
                cmd!("cmp retval, 0"),
                cmd!("jne {}", yes_label),
                cmd!("jmp {}", no_label),
                cmd!("{}: ; yes branch", yes_label),
                compile_expr(ctx, *yes)?,
                cmd!("jmp {}", finish_label),
                cmd!("{}: ; no branch", no_label),
                compile_expr(ctx, *no)?,
                cmd!("{}:", finish_label),
                cmd!("; end conditional")
            ])
        }
        ParenExpression::Equals { first, second } => {
            let not_equal_label = ctx.new_label();
            let finish_label = ctx.new_label();
            Ok(join![
                cmd!("; start equals"),
                cmd!("; first argument"),
                compile_expr(ctx, *first)?,
                cmd!("push retval"),
                cmd!("push rettype"),
                cmd!("; second argument"),
                compile_expr(ctx, *second)?,
                cmd!("pop rdx"),
                cmd!("cmp rdx, rettype"),
                cmd!("jne {} ; taking not equal branch", not_equal_label),
                cmd!("pop rdx"),
                cmd!("cmp rdx, retval"),
                cmd!("jne {} ; taking not equal branch", not_equal_label),
                cmd!("; equal branch"),
                cmd!("mov retval, 1"),
                cmd!("mov rettype, num_t"),
                cmd!("jmp {}", finish_label),
                cmd!("{}: ; not equal branch", not_equal_label),
                cmd!("xor retval, retval"),
                cmd!("mov rettype, num_t"),
                cmd!("{}:", finish_label)
            ])
        }
        other => todo!("compile other parexprs like {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, process::Command, u64};

    use crate::{
        ast::{Expression, ParenExpression},
        parser::parse,
        tokeniser::tokenise,
    };

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

    macro_rules! compile_str {
        ($name:ident, $str:expr) => {
            #[test]
            fn $name() {
                let ast = parse(tokenise($str).unwrap()).unwrap();
                let filename = stringify!($name);
                write_asm_file(ast, &filename);
                run_asm_file(&filename, 0, Some(42))
            }
        };

        ($name:ident, $str:expr, $output:expr) => {
            #[test]
            fn $name() {
                let ast = parse(tokenise($str).unwrap()).unwrap();
                let filename = stringify!($name);
                write_asm_file(ast, &filename);
                run_asm_file(&filename, 0, $output)
            }
        };

        ($name:ident, $str:expr, $code:expr, $output:expr) => {
            #[test]
            fn $name() {
                let ast = parse(tokenise($str).unwrap()).unwrap();
                let filename = stringify!($name);
                write_asm_file(ast, &filename);
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

    compile_str!(compile_times, "(× 21 2)");

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

    // // TODO test print cons

    // (∘ ∅)
    //
    // = 1
    compile_test!(
        compile_null_check,
        *boxparexpr!(ParenExpression::NullCheck {
            value: Box::new(Expression::Null)
        }),
        Some(1)
    );

    // (∘ 42)
    //
    // = 0
    compile_test!(
        compile_null_check_on_number,
        *boxparexpr!(ParenExpression::NullCheck {
            value: Box::new(Expression::Number(42))
        }),
        Some(0)
    );

    // ((λ foo 42))
    //
    // = 42
    compile_test!(
        compile_lambda_application,
        *boxparexpr!(ParenExpression::Application {
            lambda: boxparexpr!(ParenExpression::Lambda {
                arg: "foo".to_string(),
                body: Box::new(Expression::Number(42))
            }),
            argument: Box::new(Expression::Null)
        })
    );

    // ((λ arg (+ arg 1)) 41)
    //
    // = 42
    compile_test!(
        compile_lambda_application_with_arg,
        *boxparexpr!(ParenExpression::Application {
            lambda: boxparexpr!(ParenExpression::Lambda {
                arg: "arg".to_string(),
                body: boxparexpr!(ParenExpression::Plus {
                    first: Box::new(Expression::Number(1)),
                    second: Box::new(Expression::Identifier("arg".to_string()))
                })
            }),
            argument: Box::new(Expression::Number(41))
        })
    );

    // (≜ captured 42
    //    ((λ arg captured) ∅)
    //
    // = 42
    compile_test!(
        compile_lambda_application_with_capture,
        *boxparexpr!(ParenExpression::Binding {
            name: "captured".to_string(),
            value: Box::new(Expression::Number(42)),
            body: boxparexpr!(ParenExpression::Application {
                lambda: boxparexpr!(ParenExpression::Lambda {
                    arg: "arg".to_string(),
                    body: Box::new(Expression::Identifier("captured".to_string()))
                }),
                argument: Box::new(Expression::Null)
            })
        })
    );

    // (≜ captured 41
    //    ((λ arg (+ arg captured)) 1)
    //
    // = 42
    compile_test!(
        compile_lambda_application_with_arg_and_capture,
        *boxparexpr!(ParenExpression::Binding {
            name: "captured".to_string(),
            value: Box::new(Expression::Number(41)),
            body: boxparexpr!(ParenExpression::Application {
                lambda: boxparexpr!(ParenExpression::Lambda {
                    arg: "arg".to_string(),
                    body: boxparexpr!(ParenExpression::Plus {
                        first: Box::new(Expression::Identifier("arg".to_string())),
                        second: Box::new(Expression::Identifier("captured".to_string()))
                    })
                }),
                argument: Box::new(Expression::Number(1))
            })
        })
    );

    compile_str!(
        compile_currying,
        "(≜ add
            (λ x
                (λ y
                    (+ x y)))
            ((add 1) 41))"
    );

    compile_str!(compile_conditional, "(? 0 99 42)");

    compile_str!(compile_equals, "(= 42 42)", Some(1));
}
