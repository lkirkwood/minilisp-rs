use anyhow::Result;

use crate::{ast::Expression, cmd, compiler::lambda::compile_lambda, join};

use super::{compile_expr, context::Context};

pub fn compile_binding(
    ctx: &mut Context,
    name: &str,
    value: Expression,
    body: Expression,
) -> Result<String> {
    let thunk_code = compile_lambda(ctx, None, value)?;
    let thunk_addr = ctx.stack_bind(name.to_string());
    let skip_label = ctx.new_label();
    Ok(join![
        cmd!("; start binding for {}", name),
        cmd!("; thunk code"),
        thunk_code,
        cmd!("sub rsp, 8"),
        cmd!("mov {}, retval", thunk_addr),
        cmd!("{}: ; binding body", skip_label),
        compile_expr(ctx, body)?,
        cmd!("; end binding for {}", name)
    ])
}

pub fn compile_ident(ctx: &mut Context, ident: &str) -> Result<String> {
    Ok(join![
        cmd!("; force thunk for {}", ident),
        cmd!("push lambda_ctx"),
        cmd!("mov lambda_ctx, {}", ctx.get(ident)?),
        cmd!("call [lambda_ctx]"),
        cmd!("pop lambda_ctx")
    ])
}
