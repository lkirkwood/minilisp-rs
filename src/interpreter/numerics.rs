use std::{collections::HashMap, rc::Rc};

use anyhow::{Result, bail};

use crate::ast::Expression;

use super::{Value, interpret_expr};

/// Performs the provided two-argument numeric operation lazily.
fn two_arg_numeric_op(
    first: Expression,
    second: Expression,
    idents: HashMap<String, Value>,
    op: Box<dyn Fn(u64, u64) -> Result<u64>>,
    op_char: char,
) -> Result<Value> {
    let first_val = interpret_expr(first, idents.clone())?;
    let second_val = interpret_expr(second, idents)?;
    Ok(Value::Application(Rc::new(move || {
        if let Value::Number(first_num) = first_val.clone().eval()?
            && let Value::Number(second_num) = second_val.clone().eval()?
        {
            Ok(Value::Number((op)(first_num, second_num)?))
        } else {
            bail!(
                "The program must be invalid, because you can't use {op_char} \
                    on non-numeric values.",
            )
        }
    })))
}

pub fn interpret_plus(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(
        first,
        second,
        idents,
        Box::new(|n0, n1| match n0.checked_add(n1) {
            Some(result) => Ok(result),
            None => bail!("Integer addition of {n0} and {n1} overflowed."),
        }),
        '+',
    )
}

pub fn interpret_monus(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(
        first,
        second,
        idents,
        Box::new(|n0, n1| Ok(n0.saturating_sub(n1))),
        '−',
    )
}
pub fn interpret_times(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(first, second, idents, Box::new(|n0, n1| Ok(n0 * n1)), '×')
}

pub fn interpret_equals(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(
        first,
        second,
        idents,
        Box::new(|n0, n1| Ok(u64::from(n0 == n1))),
        '=',
    )
}

pub fn interpret_less_than(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(
        first,
        second,
        idents,
        Box::new(|n0, n1| Ok(u64::from(n0 < n1))),
        '‹',
    )
}

pub fn interpret_greater_than(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(
        first,
        second,
        idents,
        Box::new(|n0, n1| Ok(u64::from(n0 > n1))),
        '›',
    )
}

pub fn interpret_logical_and(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(
        first,
        second,
        idents,
        Box::new(|n0, n1| Ok(u64::from(n0 != 0 && n1 != 0))),
        '∧',
    )
}

pub fn interpret_logical_or(
    idents: HashMap<String, Value>,
    first: Expression,
    second: Expression,
) -> Result<Value> {
    two_arg_numeric_op(
        first,
        second,
        idents,
        Box::new(|n0, n1| Ok(u64::from(n0 != 0 || n1 != 0))),
        '∨',
    )
}

pub fn interpret_logical_not(idents: &HashMap<String, Value>, value: Expression) -> Result<Value> {
    let value = interpret_expr(value, idents.clone())?;
    Ok(Value::Application(Rc::new(move || {
        if let Value::Number(value_num) = value.clone().eval()? {
            Ok(Value::Number(u64::from(value_num == 0)))
        } else {
            bail!(
                "The program must be invalid, because you can't use \
                                ¬ on a non-numeric value."
            )
        }
    })))
}
