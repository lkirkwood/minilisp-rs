use std::{collections::HashMap, rc::Rc};

use anyhow::{Result, bail};

use crate::ast::Expression;

use super::{Value, interpret_expr};

pub fn interpret_cons(
    car: Expression,
    cdr: Expression,
    idents: HashMap<String, Value>,
) -> Result<Value> {
    Ok(Value::Cons((
        Box::new(interpret_expr(car, idents.clone())?),
        Box::new(interpret_expr(cdr, idents)?),
    )))
}

pub fn interpret_car(cons: Expression, idents: HashMap<String, Value>) -> Result<Value> {
    let cons_val = interpret_expr(cons, idents)?;
    Ok(Value::Application(Rc::new(move || {
        if let Value::Cons(cons_cell) = cons_val.clone().eval()? {
            Ok(*cons_cell.0)
        } else {
            bail!(
                "The program must be invalid, because \"car\" only works on \
                            cons cells, not {cons_val}"
            )
        }
    })))
}

pub fn interpret_cdr(cons: Expression, idents: HashMap<String, Value>) -> Result<Value> {
    let cons_val = interpret_expr(cons, idents)?;
    Ok(Value::Application(Rc::new(move || {
        if let Value::Cons(cons_cell) = cons_val.clone().eval()? {
            Ok(*cons_cell.1)
        } else {
            bail!(
                "The program must be invalid, because \"cdr\" only works on \
                            cons cells, not {cons_val}"
            )
        }
    })))
}
