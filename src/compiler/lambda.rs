use std::collections::HashSet;

use anyhow::Result;

use crate::{
    ast::{BoxExpr, Expression, ParenExpression},
    cmd,
    compiler::compile_expr,
    join,
};

use super::context::Context;

// Free variable analysis

/// Find the free variables referenced by the lambda.
pub fn lambda_free_vars<'a>(arg: &str, body: &'a BoxExpr) -> HashSet<&'a str> {
    let mut free_vars = expr_free_vars(body);
    free_vars.remove(arg);
    free_vars
}

fn expr_free_vars(expr: &BoxExpr) -> HashSet<&str> {
    let mut free_vars = HashSet::new();

    if let Expression::Identifier(ident) = &**expr {
        free_vars.insert(ident.as_str());
    } else if let Expression::Paren(parexpr) = &**expr {
        match &**parexpr {
            ParenExpression::Plus { first, second }
            | ParenExpression::Monus { first, second }
            | ParenExpression::Times { first, second }
            | ParenExpression::Equals { first, second }
            | ParenExpression::GreaterThan { first, second }
            | ParenExpression::LessThan { first, second }
            | ParenExpression::LogicalAnd { first, second }
            | ParenExpression::LogicalOr { first, second } => {
                free_vars.extend(expr_free_vars(first));
                free_vars.extend(expr_free_vars(second));
            }
            ParenExpression::Condition { predicate, yes, no } => {
                free_vars.extend(expr_free_vars(predicate));
                free_vars.extend(expr_free_vars(yes));
                free_vars.extend(expr_free_vars(no));
            }
            ParenExpression::Binding { name, body, .. } => {
                free_vars.extend(expr_free_vars(body));
                free_vars.remove(name.as_str());
            }
            ParenExpression::Cons { car, cdr } => {
                free_vars.extend(expr_free_vars(car));
                free_vars.extend(expr_free_vars(cdr));
            }
            ParenExpression::Car { cons } | ParenExpression::Cdr { cons } => {
                free_vars.extend(expr_free_vars(cons));
            }
            ParenExpression::NullCheck { value } | ParenExpression::LogicalNot { value } => {
                free_vars.extend(expr_free_vars(value));
            }
            ParenExpression::Application { lambda, argument } => {
                free_vars.extend(expr_free_vars(lambda));
                free_vars.extend(expr_free_vars(argument));
            }
            ParenExpression::Lambda { arg, body } => {
                free_vars.extend(lambda_free_vars(arg, body));
            }
        }
    }

    free_vars
}

// Emitting ASM

/// Compile a lambda to ASM.
pub fn compile_lambda(ctx: &mut Context, arg: String, body: BoxExpr) -> Result<String> {
    let free_vars = lambda_free_vars(&arg, &body);
    // 8 bytes for value and 8 for type per free var,
    // 8 bytes for address of body label, and 16 for arg value and type.
    let heap_space = free_vars.len() * 16 + 24;
    let body_label = ctx.new_label();
    let epilogue_label = ctx.new_label();

    let mut prologue = join![
        cmd!("; start lambda prologue"),
        cmd!("mov rdx, {}", heap_space),
        cmd!("call ensure_mem"),
        cmd!("lea rdx, [rel {}]", body_label),
        cmd!("mov [heap_start], rdx")
    ];

    let mut offset = 8; // first qword of heap data is addr of body label

    ctx.bind(arg, format!("[lambda_ctx + {}]", offset + 8));
    offset += 16;

    for var in free_vars {
        let addr = ctx.get(var)?;
        prologue.push_str(&join![
            cmd!("; copying {} to lambda heap section", var),
            // value
            cmd!("mov qword retval, {}", addr),
            cmd!("mov [heap_start + {}], retval", offset + 8),
            // type
            cmd!("lea rettype, {}", addr),
            cmd!("mov qword rettype, [rettype - 8]"),
            cmd!("mov [heap_start + {}], rettype", offset)
        ]);

        ctx.bind(var.to_string(), format!("[lambda_ctx + {}]", offset + 8));
        offset += 16;
    }

    prologue.push_str(&join![
        cmd!("push heap_start"),
        cmd!(
            "; allocate for {} vars, input arg, and function ptr",
            (offset - 24) / 16
        ),
        cmd!("add heap_start, {}", offset),
        cmd!("jmp {}", epilogue_label),
        cmd!("; end lambda prologue")
    ]);

    let body_code = compile_expr(ctx, *body)?;

    Ok(join![
        cmd!("; start lambda"),
        prologue,
        cmd!("; start body of lambda"),
        cmd!("{}:", body_label),
        body_code,
        cmd!("ret"),
        cmd!("; end body of lambda"),
        cmd!("; start lambda epilogue"),
        cmd!("{}:", epilogue_label),
        cmd!("pop retval ; old start of heap"),
        cmd!("mov qword rettype, lambda_t"),
        cmd!("; end lambda")
    ])
}

pub fn compile_application(
    ctx: &mut Context,
    lambda: Expression,
    argument: Expression,
) -> Result<String> {
    let arg_code = compile_expr(ctx, argument)?;
    ctx.stack_alloc(16);
    let lambda_code = compile_expr(ctx, lambda)?;
    ctx.stack_free(16);
    Ok(join![
        cmd!("; start lambda application"),
        cmd!("; compute argument"),
        arg_code,
        cmd!("; store argument"),
        cmd!("push retval"),
        cmd!("push rettype"),
        cmd!("; compute lambda"),
        lambda_code,
        cmd!("; set up lambda call"),
        cmd!("mov lambda_ctx, retval"),
        cmd!("pop rettype"),
        cmd!("pop retval"),
        cmd!("mov [lambda_ctx + 8], rettype"),
        cmd!("mov [lambda_ctx + 16], retval"),
        cmd!("call [lambda_ctx]")
    ])
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::ast::{Expression, ParenExpression};

    use super::lambda_free_vars;

    #[test]
    fn free_var_simple() {
        let body = Box::new(Expression::Identifier("foo".to_string()));
        let free_vars = lambda_free_vars("", &body);
        assert_eq!(free_vars, HashSet::from(["foo"]));
    }

    #[test]
    fn free_var_simple_many() {
        let body = boxparexpr!(ParenExpression::Cons {
            car: Box::new(Expression::Identifier("foo".to_string())),
            cdr: Box::new(Expression::Identifier("bar".to_string()))
        });
        let free_vars = lambda_free_vars("", &body);
        assert_eq!(free_vars, HashSet::from(["foo", "bar"]));
    }

    #[test]
    fn free_var_not_arg() {
        let body = Box::new(Expression::Identifier("foo".to_string()));
        let free_vars = lambda_free_vars("foo", &body);
        assert!(free_vars.is_empty());
    }

    #[test]
    fn free_var_not_arg_but_others() {
        let body = boxparexpr!(ParenExpression::Cons {
            car: Box::new(Expression::Identifier("foo".to_string())),
            cdr: Box::new(Expression::Identifier("bar".to_string()))
        });
        let free_vars = lambda_free_vars("foo", &body);
        assert_eq!(free_vars, HashSet::from(["bar"]));
    }

    #[test]
    fn free_var_not_inner() {
        let body = boxparexpr!(ParenExpression::Binding {
            name: "inner".to_string(),
            value: Box::new(Expression::Number(42)),
            body: Box::new(Expression::Identifier("inner".to_string()))
        });
        let free_vars = lambda_free_vars("", &body);
        assert!(free_vars.is_empty());
    }

    #[test]
    fn free_var_when_shadowed_by_inner() {
        let body = boxparexpr!(ParenExpression::Cons {
            car: Box::new(Expression::Identifier("free".to_string())),
            cdr: boxparexpr!(ParenExpression::Binding {
                name: "free".to_string(),
                value: Box::new(Expression::Number(42)),
                body: Box::new(Expression::Identifier("free".to_string()))
            })
        });
        let free_vars = lambda_free_vars("", &body);
        assert_eq!(free_vars, HashSet::from(["free"]));
    }
}
