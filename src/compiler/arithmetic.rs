use anyhow::Result;

use crate::{ast::Expression, cmd, compiler::compile_expr, join};

use super::context::Context;

pub fn compile_plus(ctx: &mut Context, first: Expression, second: Expression) -> Result<String> {
    let first = compile_expr(ctx, first)?;
    ctx.stack_alloc(8);
    let second = compile_expr(ctx, second)?;
    ctx.stack_free(8);
    Ok(join![
        cmd!("; begin plus"),
        cmd!("; compute first plus operand"),
        first,
        cmd!("; store first plus operand"),
        cmd!("push retval"),
        cmd!("; compute second plus operand"),
        second,
        cmd!("pop rax"),
        cmd!("add retval, rax"),
        cmd!("jc generic_error"),
        cmd!("; end plus")
    ])
}

pub fn compile_monus(ctx: &mut Context, first: Expression, second: Expression) -> Result<String> {
    let calc_label = ctx.new_label();
    let end_label = ctx.new_label();
    let second = compile_expr(ctx, second)?;
    ctx.stack_alloc(8);
    let first = compile_expr(ctx, first)?;
    ctx.stack_free(8);
    Ok(join![
        cmd!("; begin monus"),
        cmd!("; compute second monus operand first"),
        second,
        cmd!("; store second monus operand"),
        cmd!("push retval"),
        cmd!("; compute first monus operand now"),
        first,
        cmd!("pop rax"),
        cmd!("cmp retval, rax"),
        cmd!("jg {}", calc_label),
        cmd!("xor retval, retval"),
        cmd!("jmp {}", end_label),
        cmd!("{}: ; perform calculation", calc_label),
        cmd!("sub retval, rax"),
        cmd!("{}: ; end of calculation", end_label),
        cmd!("; end monus")
    ])
}

pub fn compile_times(ctx: &mut Context, first: Expression, second: Expression) -> Result<String> {
    let first = compile_expr(ctx, first)?;
    let second = compile_expr(ctx, second)?;
    Ok(join![
        cmd!("; begin times"),
        cmd!("; compute first times operand"),
        first,
        cmd!("; store first times operand"),
        cmd!("push retval"),
        cmd!("; compute second times operand"),
        second,
        cmd!("pop rax"),
        cmd!("mul retval"),
        cmd!("mov retval, rax"),
        cmd!("jc generic_error"),
        cmd!("; end times")
    ])
}

pub fn compile_equals(ctx: &mut Context, first: Expression, second: Expression) -> Result<String> {
    let not_equal_label = ctx.new_label();
    let finish_label = ctx.new_label();
    Ok(join![
        cmd!("; start equals"),
        cmd!("; first argument"),
        compile_expr(ctx, first)?,
        cmd!("push retval"),
        cmd!("push rettype"),
        cmd!("; second argument"),
        compile_expr(ctx, second)?,
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
