use std::collections::{HashMap, hash_map::Entry};

// TODO remove this for something lighter
use rand::random_range;

use crate::ast::{BoxExpr, Expression, ParenExpression};

const MAX_DEPTH: usize = 10;

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
    fn random_expr_fn(&self) -> Box<dyn Fn(Context) -> BoxExpr + '_> {
        match self {
            ValueType::Null => Box::new(random_null) as Box<dyn Fn(Context) -> BoxExpr>,
            ValueType::Number => Box::new(random_number) as Box<dyn Fn(Context) -> BoxExpr>,
            ValueType::Cons((car_target, cdr_target)) => Box::new(|context| {
                random_cons(context, &(*car_target.clone(), *cdr_target.clone()))
            })
                as Box<dyn Fn(Context) -> BoxExpr>,
            ValueType::Lambda(target_type) => {
                Box::new(|context| random_lambda(context, *target_type.clone()))
                    as Box<dyn Fn(Context) -> BoxExpr>
            }
            ValueType::Boolean => Box::new(random_bool) as Box<dyn Fn(Context) -> BoxExpr>,
        }
    }
}

// TODO change to Context, add depth control
#[derive(Clone)]
struct Context {
    ident_value_types: HashMap<String, ValueType>,
    value_type_idents: HashMap<ValueType, Vec<String>>,
    depth: usize,
}

impl Context {
    /// Bind an identifier to the given `ValueType`.
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

    /// Return a random identifier with the given `ValueType`.
    fn random_choice(&self, value_type: &ValueType) -> Option<&str> {
        if let Some(idents) = self.value_type_idents.get(value_type)
            && !idents.is_empty()
        {
            Some(&idents[random_range(0..idents.len())])
        } else {
            None
        }
    }

    /// Return a new `Context` with an increased depth.
    fn deeper(mut self) -> Self {
        self.depth += 1;
        self
    }
}

/// Produces a random AST for a valid minilisp program.
pub fn random_program() -> BoxExpr {
    random_expr(Context {
        value_type_idents: HashMap::new(),
        ident_value_types: HashMap::new(),
        depth: 0,
    })
}

fn random_expr(context: Context) -> BoxExpr {
    if context.depth > MAX_DEPTH {
        random_number(context.deeper())
    } else {
        match random_range(0..4) {
            0 => random_null(context.deeper()),
            1 => random_number(context.deeper()),
            2 => random_cons(
                context.deeper(),
                &(ValueType::random(), ValueType::random()),
            ),
            3 => random_lambda(context.deeper(), ValueType::random()),
            _ => unreachable!(),
        }
    }
}

fn random_null(context: Context) -> BoxExpr {
    let mut random_num = random_range(0..4);
    if random_num == 3 {
        if let Some(ident) = context.random_choice(&ValueType::Null) {
            return Box::new(Expression::Identifier(ident.to_string()));
        }
        random_num = random_range(0..3);
    }

    if context.depth > MAX_DEPTH {
        Box::new(Expression::Null)
    } else {
        match random_num {
            0 => Box::new(Expression::Null),
            1 => random_paren_expr(context.deeper(), &ValueType::Null),
            2 => random_expr(context.deeper()),
            _ => unreachable!(),
        }
    }
}

fn random_number(context: Context) -> BoxExpr {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(ident) = context.random_choice(&ValueType::Number) {
            return Box::new(Expression::Identifier(ident.to_string()));
        }
        random_num = random_range(0..2);
    }

    if context.depth > MAX_DEPTH {
        Box::new(Expression::Number(random_range(0..100) as isize))
    } else {
        match random_num {
            0 => Box::new(Expression::Number(random_range(0..100) as isize)),
            1 => random_paren_expr(context.deeper(), &ValueType::Number),
            _ => unreachable!(),
        }
    }
}

fn random_cons(mut context: Context, target_type: &(ValueType, ValueType)) -> BoxExpr {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(ident) = context.random_choice(&ValueType::Cons((
            Box::new(target_type.0.clone()),
            Box::new(target_type.1.clone()),
        ))) {
            return Box::new(Expression::Identifier(ident.to_string()));
        }
        random_num = random_range(0..2);
    }

    context = context.deeper();
    match random_num {
        0 => boxparexpr!(ParenExpression::Cons {
            car: target_type.0.random_expr_fn()(context.clone()),
            cdr: target_type.1.random_expr_fn()(context)
        }),
        1 => random_paren_expr(
            context,
            &ValueType::Cons((
                Box::new(target_type.0.clone()),
                Box::new(target_type.1.clone()),
            )),
        ),
        _ => unreachable!(),
    }
}

fn random_bool(context: Context) -> BoxExpr {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(boolean) = context.random_choice(&ValueType::Boolean) {
            return Box::new(Expression::Identifier(boolean.to_string()));
        }
        random_num = random_range(0..2);
    }

    match random_num {
        0 => random_number(context.deeper()),
        1 => random_null(context.deeper()),
        _ => unreachable!(),
    }
}

fn random_lambda(context: Context, target_type: ValueType) -> BoxExpr {
    let mut random_num = random_range(0..3);
    if random_num == 2 {
        if let Some(lambda) =
            context.random_choice(&ValueType::Lambda(Box::new(target_type.clone())))
        {
            return Box::new(Expression::Identifier(lambda.to_string()));
        }
        random_num = random_range(0..2);
    }

    match random_num {
        0 => boxparexpr!(ParenExpression::Lambda {
            arg: random_string(),
            body: target_type.random_expr_fn()(context.deeper())
        }),
        1 => random_paren_expr(context.deeper(), &ValueType::Lambda(Box::new(target_type))),
        _ => unreachable!(),
    }
}

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

macro_rules! random_two_arg_parexpr {
    ($op_variant:ident, $context:expr) => {
        boxparexpr!(ParenExpression::$op_variant {
            first: random_number($context.clone()),
            second: random_number($context),
        })
    };
}

// TODO maybe make context shared reference, just remove binding after subexpr complete
fn random_paren_expr(mut context: Context, target_type: &ValueType) -> BoxExpr {
    let random_target = target_type.random_expr_fn();
    context = context.deeper();

    let range = if matches!(
        target_type,
        ValueType::Null | ValueType::Number | ValueType::Boolean
    ) {
        if context.depth > MAX_DEPTH {
            0..10
        } else {
            0..15
        }
    } else {
        10..15
    };

    match random_range(range) {
        // number / boolean
        0 => random_two_arg_parexpr!(Plus, context),
        1 => random_two_arg_parexpr!(Minus, context),
        2 => random_two_arg_parexpr!(Times, context),
        3 => random_two_arg_parexpr!(Equals, context),
        4 => random_two_arg_parexpr!(LessThan, context),
        5 => random_two_arg_parexpr!(GreaterThan, context),
        6 => boxparexpr!(ParenExpression::LogicalAnd {
            first: random_bool(context.clone()),
            second: random_bool(context)
        }),
        7 => random_two_arg_parexpr!(LogicalOr, context),
        8 => boxparexpr!(ParenExpression::LogicalNot {
            value: random_bool(context)
        }),
        9 => boxparexpr!(ParenExpression::NullCheck {
            value: random_null(context)
        }),
        // any type
        10 => boxparexpr!(ParenExpression::Condition {
            predicate: random_bool(context.clone()),
            yes: random_target(context.clone()),
            no: random_target(context),
        }),
        11 => {
            let ident = random_string();
            let value_expr = random_target(context.clone());
            context.bind(ident.clone(), target_type.clone());

            boxparexpr!(ParenExpression::Binding {
                name: ident,
                value: value_expr,
                body: random_target(context),
            })
        }
        12 => boxparexpr!(ParenExpression::Car {
            cons: boxparexpr!(ParenExpression::Cons {
                car: random_target(context.clone()),
                cdr: random_expr(context)
            })
        }),
        13 => boxparexpr!(ParenExpression::Cdr {
            cons: boxparexpr!(ParenExpression::Cons {
                car: random_target(context.clone()),
                cdr: random_expr(context)
            })
        }),
        14 => boxparexpr!(ParenExpression::Application {
            lambda: random_lambda(context.clone(), target_type.clone()),
            argument: random_target(context)
        }),
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::{interpreter::interpret, randprog::random_ast};

    #[test]
    fn test_random_program() {
        let program = random_ast();
        fs::write("/tmp/lastprog", format!("{program:#?}")).unwrap();
        let result = interpret(program).unwrap();
        println!("{result}");
    }
}
