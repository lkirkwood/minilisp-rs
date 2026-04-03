use anyhow::Result;

use crate::{ast::Expression, cmd, compiler::compile_expr, join};

use super::context::Context;

pub fn compile_null_check(ctx: &mut Context, value: Expression) -> Result<String> {
    let value_code = compile_expr(ctx, value)?;
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

pub fn compile_condition(
    ctx: &mut Context,
    predicate: Expression,
    yes: Expression,
    no: Expression,
) -> Result<String> {
    let yes_label = ctx.new_label();
    let no_label = ctx.new_label();
    let finish_label = ctx.new_label();
    Ok(join![
        cmd!("; start conditional"),
        compile_expr(ctx, predicate)?,
        cmd!("cmp retval, 0"),
        cmd!("jne {}", yes_label),
        cmd!("jmp {}", no_label),
        cmd!("{}: ; yes branch", yes_label),
        compile_expr(ctx, yes)?,
        cmd!("jmp {}", finish_label),
        cmd!("{}: ; no branch", no_label),
        compile_expr(ctx, no)?,
        cmd!("{}:", finish_label),
        cmd!("; end conditional")
    ])
}

pub fn compile_logical_and(
    ctx: &mut Context,
    first: Expression,
    second: Expression,
) -> Result<String> {
    let finish_label = ctx.new_label();
    Ok(join![
        cmd!("; start logical and"),
        cmd!("; compute first value"),
        compile_expr(ctx, first)?,
        cmd!("cmp retval, 0"),
        cmd!("je {}", finish_label),
        cmd!("; compute second value"),
        compile_expr(ctx, second)?,
        cmd!("cmp retval, 0"),
        cmd!("je {}", finish_label),
        cmd!("mov retval, 1"),
        cmd!("{}:", finish_label),
        cmd!("mov rettype, num_t"),
        cmd!("; end logical and")
    ])
}

pub fn compile_logical_or(
    ctx: &mut Context,
    first: Expression,
    second: Expression,
) -> Result<String> {
    let true_label = ctx.new_label();
    let finish_label = ctx.new_label();
    Ok(join![
        cmd!("; start logical or"),
        cmd!("; compute first value"),
        compile_expr(ctx, first)?,
        cmd!("cmp retval, 0"),
        cmd!("jne {}", true_label),
        cmd!("; compute second value"),
        compile_expr(ctx, second)?,
        cmd!("cmp retval, 0"),
        cmd!("je {}", finish_label),
        cmd!("{}:", true_label),
        cmd!("mov retval, 1"),
        cmd!("{}:", finish_label),
        cmd!("mov rettype, num_t"),
        cmd!("; end logical or")
    ])
}

pub fn compile_logical_not(ctx: &mut Context, value: Expression) -> Result<String> {
    let value_false_label = ctx.new_label();
    let finish_label = ctx.new_label();
    Ok(join![
        cmd!("; start logical not"),
        compile_expr(ctx, value)?,
        cmd!("cmp retval, 0"),
        cmd!("je {}", value_false_label),
        cmd!("xor retval, retval"),
        cmd!("jmp {}", finish_label),
        cmd!("{}:", value_false_label),
        cmd!("mov retval, 1"),
        cmd!("{}:", finish_label),
        cmd!("mov rettype, num_t"),
        cmd!("; end logical not")
    ])
}

pub fn compile_less_than(
    ctx: &mut Context,
    first: Expression,
    second: Expression,
) -> Result<String> {
    let first_code = compile_expr(ctx, first)?;
    ctx.stack_alloc(8);
    let second_code = compile_expr(ctx, second)?;
    ctx.stack_free(8);
    let true_label = ctx.new_label();
    let false_label = ctx.new_label();
    let finish_label = ctx.new_label();
    Ok(join![
        cmd!("; start less than"),
        first_code,
        cmd!("push retval"),
        second_code,
        cmd!("pop rax"),
        cmd!("cmp rax, retval"),
        cmd!("jl {}", true_label),
        cmd!("{}:", false_label),
        cmd!("xor retval, retval"),
        cmd!("jmp {}", finish_label),
        cmd!("{}:", true_label),
        cmd!("mov retval, 1"),
        cmd!("{}:", finish_label),
        cmd!("mov rettype, num_t"),
        cmd!("; end less than")
    ])
}

pub fn compile_greater_than(
    ctx: &mut Context,
    first: Expression,
    second: Expression,
) -> Result<String> {
    let first_code = compile_expr(ctx, first)?;
    ctx.stack_alloc(8);
    let second_code = compile_expr(ctx, second)?;
    ctx.stack_free(8);
    let true_label = ctx.new_label();
    let false_label = ctx.new_label();
    let finish_label = ctx.new_label();
    Ok(join![
        cmd!("; start greater than"),
        first_code,
        cmd!("push retval"),
        second_code,
        cmd!("pop rax"),
        cmd!("cmp rax, retval"),
        cmd!("jg {}", true_label),
        cmd!("{}:", false_label),
        cmd!("xor retval, retval"),
        cmd!("jmp {}", finish_label),
        cmd!("{}:", true_label),
        cmd!("mov retval, 1"),
        cmd!("{}:", finish_label),
        cmd!("mov rettype, num_t"),
        cmd!("; end greater than")
    ])
}
