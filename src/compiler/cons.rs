use anyhow::Result;

use crate::{ast::Expression, cmd, compiler::compile_expr, join};

use super::context::Context;

#[allow(clippy::similar_names)]
pub fn compile_cons(ctx: &mut Context, car: Expression, cdr: Expression) -> Result<String> {
    let _heap_start = ctx.stack_alloc(8);
    let car_code = compile_expr(ctx, car)?;
    let cdr_code = compile_expr(ctx, cdr)?;
    ctx.stack_free(8);
    Ok(join![
        cmd!("; start cons"),
        cmd!("; allocate heap space"),
        cmd!("mov rdx, 32"),
        cmd!("push lambda_ctx"),
        cmd!("call ensure_mem"),
        cmd!("pop lambda_ctx"),
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

pub fn compile_car(ctx: &mut Context, cons: Expression) -> Result<String> {
    Ok(join![
        compile_expr(ctx, cons)?,
        cmd!("; get car from cons"),
        cmd!("mov rdi, retval"),
        cmd!("add rdi, 8"),
        cmd!("mov retval, [retval]"),
        cmd!("mov rettype, [rdi]"),
        cmd!("; end car")
    ])
}

pub fn compile_cdr(ctx: &mut Context, cons: Expression) -> Result<String> {
    Ok(join![
        compile_expr(ctx, cons)?,
        cmd!("; get cdr from cons"),
        cmd!("add retval, 16"),
        cmd!("mov rdi, retval"),
        cmd!("add rdi, 8"),
        cmd!("mov retval, [retval]"),
        cmd!("mov rettype, [rdi]"),
        cmd!("; end cdr")
    ])
}
