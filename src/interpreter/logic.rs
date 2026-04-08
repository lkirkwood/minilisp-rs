use std::{collections::HashMap, rc::Rc};

use anyhow::Result;

use crate::ast::Expression;

use super::{Value, interpret_expr};

pub fn interpret_condition(
    idents: HashMap<String, Value>,
    predicate: Expression,
    yes: Expression,
    no: Expression,
) -> Result<Value> {
    if interpret_expr(predicate, idents.clone())?.truthy()? {
        interpret_expr(yes, idents)
    } else {
        interpret_expr(no, idents)
    }
}

pub fn interpret_binding(
    mut idents: HashMap<String, Value>,
    name: String,
    value: Expression,
    body: Expression,
) -> Result<Value> {
    idents.insert(name, interpret_expr(value, idents.clone())?);
    interpret_expr(body, idents)
}

pub fn interpret_null_check(idents: HashMap<String, Value>, value: Expression) -> Result<Value> {
    let value = interpret_expr(value, idents)?;
    Ok(Value::Application(Rc::new(move || {
        if let Value::Null = value.clone().eval()? {
            Ok(Value::Number(1))
        } else {
            Ok(Value::Number(0))
        }
    })))
}
