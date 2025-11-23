use std::collections::{HashMap, hash_map::Entry};

use anyhow::Result;
// TODO remove this for something lighter
use rand::random_range;

use crate::ast::{BoxExpr, Expression, ParenExpression};

fn random_string() -> String {
    let mut string = String::with_capacity(10);
    for _ in 0..=10 {
        match char::from_u32(random_range(97..=122)) {
            None => unreachable!(),
            Some(random_char) => string.push(random_char),
        }
    }
    string
}

/// Represents the different types of value an expression can evaluate to.
#[derive(Clone, PartialEq, Eq, Hash)]
enum ValueType {
    Null,
    Number,
    Cons((Box<ValueType>, Box<ValueType>)),
    Lambda(Box<ValueType>),
    Boolean,
}

impl ValueType {
    /// Returns a random instance of `ValueType`.
    fn random() -> Self {
        match random_range(0..5) {
            0 => Self::Null,
            1 => Self::Number,
            2 => Self::Cons((
                Box::new(ValueType::random()),
                (Box::new(ValueType::random())),
            )),
            3 => Self::Lambda(Box::new(ValueType::random())),
            4 => Self::Boolean,
            _ => unreachable!(),
        }
    }

    /// Returns a pointer to a function which, when called, will produce a random
    /// expression of this value type.
    fn random_expr_fn(&self) -> Box<dyn Fn(Bindings) -> Result<BoxExpr> + '_> {
        match self {
            ValueType::Null => Box::new(random_null) as Box<dyn Fn(Bindings) -> Result<BoxExpr>>,
            ValueType::Number => {
                Box::new(random_number) as Box<dyn Fn(Bindings) -> Result<BoxExpr>>
            }
            ValueType::Cons((car_target, cdr_target)) => Box::new(|bindings| {
                random_cons(bindings, (*car_target.clone(), *cdr_target.clone()))
            })
                as Box<dyn Fn(Bindings) -> Result<BoxExpr>>,
            ValueType::Lambda(target_type) => {
                Box::new(|bindings| random_lambda(bindings, *target_type.clone()))
                    as Box<dyn Fn(Bindings) -> Result<BoxExpr>>
            }
            ValueType::Boolean => Box::new(random_bool) as Box<dyn Fn(Bindings) -> Result<BoxExpr>>,
        }
    }
}

// TODO change to Context, add depth control
#[derive(Clone)]
struct Bindings {
    ident_value_types: HashMap<String, ValueType>,
    value_type_idents: HashMap<ValueType, Vec<String>>,
}

impl Bindings {
    fn bind(&mut self, ident: String, value_type: ValueType) {
        self.ident_value_types
            .insert(ident.clone(), value_type.clone());

        match self.value_type_idents.entry(value_type) {
            Entry::Vacant(entry) => {
                entry.insert(vec![ident]);
            }
            Entry::Occupied(mut entry) => {
                entry.get_mut().push(ident);
            }
        }
    }

    fn random_choice(&self, value_type: &ValueType) -> Option<&str> {
        if let Some(idents) = self.value_type_idents.get(value_type)
            && !idents.is_empty()
        {
            Some(&idents[random_range(0..idents.len())])
        } else {
            None
        }
    }
}

/// Produces a random AST for a valid minilisp program.
pub fn random_program() -> Result<BoxExpr> {
    random_expr(Bindings {
        value_type_idents: HashMap::new(),
        ident_value_types: HashMap::new(),
    })
}

fn random_expr(bindings: Bindings) -> Result<BoxExpr> {
    match random_range(0..4) {
        0 => random_null(bindings),
        1 => random_number(bindings),
        2 => random_cons(bindings, (ValueType::random(), ValueType::random())),
        3 => random_lambda(bindings, ValueType::random()),
        _ => unreachable!(),
    }
}

fn random_null(bindings: Bindings) -> Result<BoxExpr> {
    let mut random_num = random_range(0..4);
    if random_num == 3 {
        if let Some(ident) = bindings.random_choice(&ValueType::Null) {
            return Ok(Box::new(Expression::Identifier(ident.to_string())));
        } else {
            random_num = random_range(0..3);
        }
    }

    match random_num {
        0 => Ok(Box::new(Expression::Null)),
        1 => random_paren_expr(bindings, ValueType::Null),
        2 => random_expr(bindings),
        _ => unreachable!(),
    }
}

fn random_number(bindings: Bindings) -> Result<BoxExpr> {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(ident) = bindings.random_choice(&ValueType::Number) {
            return Ok(Box::new(Expression::Identifier(ident.to_string())));
        }
        random_num = random_range(0..2);
    }

    match random_num {
        0 => Ok(Box::new(Expression::Number(random_range(0..100)))),
        1 => random_paren_expr(bindings, ValueType::Number),
        _ => unreachable!(),
    }
}

fn random_cons(bindings: Bindings, target_type: (ValueType, ValueType)) -> Result<BoxExpr> {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(ident) = bindings.random_choice(&ValueType::Cons((
            Box::new(target_type.0.clone()),
            Box::new(target_type.1.clone()),
        ))) {
            return Ok(Box::new(Expression::Identifier(ident.to_string())));
        } else {
            random_num = random_range(0..2);
        }
    }

    match random_num {
        0 => Ok(boxparexpr!(ParenExpression::Cons {
            car: random_expr(bindings.clone())?,
            cdr: random_expr(bindings)?,
        })),
        1 => random_paren_expr(
            bindings,
            ValueType::Cons((
                Box::new(target_type.0.clone()),
                Box::new(target_type.1.clone()),
            )),
        ),
        _ => unreachable!(),
    }
}

fn random_bool(bindings: Bindings) -> Result<BoxExpr> {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(boolean) = bindings.random_choice(&ValueType::Boolean) {
            return Ok(Box::new(Expression::Identifier(boolean.to_string())));
        }
        random_num = random_range(0..2);
    }

    match random_num {
        0 => random_number(bindings),
        1 => random_null(bindings),
        _ => unreachable!(),
    }
}

fn random_lambda(bindings: Bindings, target_type: ValueType) -> Result<BoxExpr> {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(lambda) =
            bindings.random_choice(&ValueType::Lambda(Box::new(target_type.clone())))
        {
            return Ok(Box::new(Expression::Identifier(lambda.to_string())));
        }
        random_num = random_range(0..2);
    }

    match random_num {
        0 => Ok(boxparexpr!(ParenExpression::Lambda {
            arg: random_string(),
            body: target_type.random_expr_fn()(bindings)?
        })),
        1 => random_paren_expr(bindings, ValueType::Lambda(Box::new(target_type))),
        _ => unreachable!(),
    }
}

macro_rules! random_two_arg_parexpr {
    ($op_variant:ident, $bindings:expr) => {
        boxparexpr!(ParenExpression::$op_variant {
            first: random_number($bindings.clone())?,
            second: random_number($bindings)?,
        })
    };
}

// TODO maybe make bindings shared reference, just remove binding after subexpr complete
fn random_paren_expr(mut bindings: Bindings, target_type: ValueType) -> Result<BoxExpr> {
    let random_target = target_type.random_expr_fn();

    match random_range(0..15) {
        // number / boolean
        0 => Ok(random_two_arg_parexpr!(Plus, bindings)),
        1 => Ok(random_two_arg_parexpr!(Minus, bindings)),
        2 => Ok(random_two_arg_parexpr!(Times, bindings)),
        3 => Ok(random_two_arg_parexpr!(Equals, bindings)),
        4 => Ok(random_two_arg_parexpr!(LessThan, bindings)),
        5 => Ok(random_two_arg_parexpr!(GreaterThan, bindings)),
        6 => Ok(boxparexpr!(ParenExpression::LogicalAnd {
            first: random_bool(bindings.clone())?,
            second: random_bool(bindings)?
        })),
        7 => Ok(random_two_arg_parexpr!(LogicalOr, bindings)),
        8 => Ok(boxparexpr!(ParenExpression::LogicalNot {
            value: random_bool(bindings)?
        })),
        9 => Ok(boxparexpr!(ParenExpression::NullCheck {
            value: random_null(bindings)?
        })),
        // any type
        10 => Ok(boxparexpr!(ParenExpression::Condition {
            predicate: random_bool(bindings.clone())?,
            yes: random_target(bindings.clone())?,
            no: random_target(bindings)?,
        })),
        11 => {
            let ident = random_string();
            // let value_expr = random_expr(bindings.clone())?;
            // let value_type = interpret(value_expr.clone())?.try_into()?;
            let value_expr = random_target(bindings.clone())?;
            bindings.bind(ident.clone(), target_type.clone());

            Ok(boxparexpr!(ParenExpression::Binding {
                name: ident,
                value: value_expr,
                body: random_target(bindings)?,
            }))
        }
        12 => Ok(boxparexpr!(ParenExpression::Car {
            cons: boxparexpr!(ParenExpression::Cons {
                car: random_target(bindings.clone())?,
                cdr: random_expr(bindings)?
            })
        })),
        13 => Ok(boxparexpr!(ParenExpression::Cdr {
            cons: boxparexpr!(ParenExpression::Cons {
                car: random_target(bindings.clone())?,
                cdr: random_expr(bindings)?
            })
        })),
        14 => Ok(boxparexpr!(ParenExpression::Application {
            lambda: random_lambda(bindings.clone(), target_type.clone())?,
            argument: random_target(bindings)?
        })),
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::{interpreter::interpret, randprog::random_program};

    #[test]
    fn test_random_program() {
        let program = random_program().unwrap();
        fs::write("/tmp/lastprog", format!("{program:#?}")).unwrap();
        let result = interpret(program).unwrap();
        println!("{result}");
    }
}
