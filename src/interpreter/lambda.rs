use std::{collections::HashMap, rc::Rc};

use anyhow::{Result, bail};

use crate::ast::Expression;

use super::{Lambda, Value, interpret_expr};

pub fn interpret_lambda(idents: HashMap<String, Value>, arg: String, body: Expression) -> Value {
    Value::Lambda(Lambda {
        arg: arg.clone(),
        body_expr: body.clone(),
        func: Rc::new(move |value| {
            let mut local_idents = idents.clone();
            local_idents.insert(arg.clone(), value);
            interpret_expr(body.clone(), local_idents)
        }),
    })
}

pub fn interpret_application(
    idents: HashMap<String, Value>,
    lambda: Expression,
    argument: Expression,
) -> Result<Value> {
    let lambda_val = interpret_expr(lambda, idents.clone())?;
    let arg_val = interpret_expr(argument, idents)?;

    if let Value::Lambda(lambda) = lambda_val {
        Ok(Value::Application(Rc::new(move || {
            lambda.clone().call(arg_val.clone())
        })))
    } else if let Value::Application(_) = lambda_val {
        Ok(Value::Application(Rc::new(move || {
            let evaluated = lambda_val.clone().eval()?;
            if let Value::Lambda(lambda) = evaluated {
                lambda.call(arg_val.clone())
            } else {
                bail!(
                    "The program must be invalid, because lambda application was used \
                            lazily on something that was not a lambda - instead it was: {evaluated}"
                )
            }
        })))
    } else {
        bail!(
            "The program must be invalid, because lambda application was used \
                    on something that was not a lambda - instead it was: {lambda_val}"
        )
    }
}
