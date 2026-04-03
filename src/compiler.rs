mod arithmetic;
mod bindings;
mod cons;
mod context;
mod lambda;
mod logic;

use anyhow::Result;
use arithmetic::{compile_equals, compile_monus, compile_plus, compile_times};
use bindings::{compile_binding, compile_ident};
use cons::{compile_car, compile_cdr, compile_cons};
use lambda::{compile_application, compile_lambda};
use logic::{
    compile_condition, compile_greater_than, compile_less_than, compile_logical_and,
    compile_logical_not, compile_logical_or, compile_null_check,
};

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
        Expression::Identifier(ident) => compile_ident(ctx, &ident),
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
        ParenExpression::Plus { first, second } => compile_plus(ctx, *first, *second),
        ParenExpression::Monus { first, second } => compile_monus(ctx, *first, *second),
        ParenExpression::Times { first, second } => compile_times(ctx, *first, *second),
        ParenExpression::Equals { first, second } => compile_equals(ctx, *first, *second),
        ParenExpression::Binding { name, value, body } => {
            compile_binding(ctx, &name, *value, *body)
        }
        ParenExpression::Cons { car, cdr } => compile_cons(ctx, *car, *cdr),
        ParenExpression::Car { cons } => compile_car(ctx, *cons),
        ParenExpression::Cdr { cons } => compile_cdr(ctx, *cons),
        ParenExpression::Lambda { arg, body } => compile_lambda(ctx, Some(arg), *body),
        ParenExpression::Application { lambda, argument } => {
            compile_application(ctx, *lambda, *argument)
        }
        ParenExpression::NullCheck { value } => compile_null_check(ctx, *value),
        ParenExpression::Condition { predicate, yes, no } => {
            compile_condition(ctx, *predicate, *yes, *no)
        }
        ParenExpression::LogicalAnd { first, second } => compile_logical_and(ctx, *first, *second),
        ParenExpression::LogicalOr { first, second } => compile_logical_or(ctx, *first, *second),
        ParenExpression::LogicalNot { value } => compile_logical_not(ctx, *value),
        ParenExpression::LessThan { first, second } => compile_less_than(ctx, *first, *second),
        ParenExpression::GreaterThan { first, second } => {
            compile_greater_than(ctx, *first, *second)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, process::Command, u64};

    use crate::{ast::Expression, parser::parse, tokeniser::tokenise};

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

    compile_str!(compile_num, "42");

    compile_str!(compile_plus, "(+ 41 1)");

    // (+ INT_MAX 1)
    //
    // = overflow error
    compile_str!(
        compile_plus_overflow_error,
        &format!("(+ {} 1)", u64::MAX),
        1,
        None
    );

    compile_str!(
        compile_plus_overflow_almost,
        &format!("(+ {} 0)", u64::MAX),
        Some(u64::MAX)
    );

    compile_str!(compile_monus, "(− 43 1)");

    compile_str!(compile_monus_saturates, "(− 1 42)", Some(0));

    compile_str!(compile_times, "(× 21 2)");

    compile_str!(compile_equals, "(= 42 42)", Some(1));

    compile_str!(compile_ident, "(≜ foo 42 foo)");

    compile_str!(compile_ident_plus, "(≜ foo 41 (≜ bar 1 (+ foo bar)))");

    compile_str!(compile_cons_car, "(≜ foo (∷ 42 99) (← foo))");

    compile_str!(compile_cons_cdr, "(≜ foo (∷ 99 42) (→ foo))");

    compile_str!(compile_null_check, "(∘ ∅)", Some(1));

    compile_str!(compile_null_check_on_number, "(∘ 42)", Some(0));

    compile_str!(compile_lambda_application, "((λ foo 42) ∅)");

    compile_str!(
        compile_lambda_application_with_arg,
        "((λ arg (+ arg 1)) 41)"
    );

    compile_str!(
        compile_lambda_application_with_capture,
        "(≜ captured 42 ((λ arg captured) ∅))"
    );

    compile_str!(
        compile_lambda_application_with_arg_and_capture,
        "(≜ captured 41 ((λ arg (+ arg captured)) 1))"
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

    compile_str!(compile_logical_and_true, "(∧ 42 99)", Some(1));

    compile_str!(compile_logical_and_one_false, "(∧ 0 99)", Some(0));

    compile_str!(compile_logical_and_other_false, "(∧ 42 0)", Some(0));

    compile_str!(compile_logical_and_both_false, "(∧ 0 0)", Some(0));

    compile_str!(compile_logical_or_both_true, "(∨ 42 99)", Some(1));

    compile_str!(compile_logical_or_one_true, "(∨ 42 0)", Some(1));

    compile_str!(compile_logical_or_other_true, "(∨ 0 99)", Some(1));

    compile_str!(compile_logical_false, "(∨ 0 0)", Some(0));

    compile_str!(compile_logical_not_true, "(¬ 0)", Some(1));

    compile_str!(compile_logical_not_false, "(¬ 42)", Some(0));

    compile_str!(compile_less_than_true, "(‹ 42 99)", Some(1));

    compile_str!(compile_less_than_false, "(‹ 42 0)", Some(0));

    compile_str!(compile_less_than_equal_false, "(‹ 42 42)", Some(0));

    compile_str!(compile_greater_than_true, "(› 42 0)", Some(1));

    compile_str!(compile_greater_than_false, "(› 0 99)", Some(0));

    compile_str!(compile_greater_than_equal_false, "(› 42 42)", Some(0));

    compile_str!(
        compile_omega_comb_lazily,
        "(≜ omega-combinator
            ((λ x (x x)) (λ x (x x)))
            ((λ x 42) omega-combinator))"
    );

    compile_str!(
        compile_lambda_as_arg,
        "(λ f
            (λ g
               (f g)))",
        0,
        None
    );

    compile_str!(
        compile_y_combinator,
        "(≜ Y
            (λ f ((λ x (f (x x))) (λ x (f (x x)))))
            ((Y (λ r (λ n (+ n 1)))) 41))"
    );

    compile_str!(
        compile_y_combinator_factorial,
        "(≜ Y
            (λ f ((λ x (f (x x))) (λ x (f (x x)))))
            (≜ factorial
                (Y (λ f
                    (λ n
                        (? (= n 0)
                            1
                            (× n (f (− n 1)))))))
                (factorial 5)))",
        Some(120)
    );

    compile_str!(
        compile_z_combinator,
        "(≜ Z
            (λ f
               ((λ x (f (λ v ((x x) v))))
                   (λ x (f (λ v ((x x) v))))))
            (≜ G
               (λ r (λ n (+ n 1)))
               (≜ add-one
                  (Z G)
                  (add-one 1))))",
        Some(2)
    );

    compile_str!(
        compile_fibonacci,
        "(≜ Y
            (λ f ((λ x (f (x x))) (λ x (f (x x)))))
            (≜ fib
                (Y (λ f
                    (λ n (? (= n 0)
                        0
                        (? (= n 1)
                            1
                            (+ (f (− n 1)) (f (− n 2))))))))
                (fib 10)))",
        Some(55)
    );

    compile_str!(
        compile_list_length,
        "(≜ Y
            (λ f ((λ x (f (x x))) (λ x (f (x x)))))
            (≜ length
               (Y (λ f (λ lst (? (∘ lst) 0 (+ 1 (f (→ lst)))))))
               (length (∷ 1 (∷ 2 (∷ 3 ∅))))))",
        Some(3)
    );
}
