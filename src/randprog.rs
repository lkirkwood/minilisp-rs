use std::collections::{HashMap, hash_map::Entry};

// TODO remove this for something lighter
use rand::random_range;

use crate::ast::{Expression, ParenExpression};

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
    fn random_expr_fn(&self) -> Box<dyn Fn(Context) -> Expression + '_> {
        match self {
            ValueType::Null => Box::new(random_null) as Box<dyn Fn(Context) -> Expression>,
            ValueType::Number => Box::new(random_number) as Box<dyn Fn(Context) -> Expression>,
            ValueType::Cons((car_target, cdr_target)) => Box::new(|context| {
                random_cons(context, &(*car_target.clone(), *cdr_target.clone()))
            })
                as Box<dyn Fn(Context) -> Expression>,
            ValueType::Lambda(target_type) => {
                Box::new(|context| random_lambda(context, *target_type.clone()))
                    as Box<dyn Fn(Context) -> Expression>
            }
            ValueType::Boolean => Box::new(random_bool) as Box<dyn Fn(Context) -> Expression>,
        }
    }
}

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

    /// Return any random identifier.
    fn random_ident(&self) -> Option<&str> {
        for idents in self.value_type_idents.values() {
            if !idents.is_empty() {
                return Some(&idents[random_range(0..idents.len())]);
            }
        }
        None
    }

    /// Return a random identifier with the given `ValueType`.
    fn random_with_type(&self, value_type: &ValueType) -> Option<&str> {
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

/// Produces a random, valid minilisp program.
pub fn random_program() -> String {
    random_ast().into()
}

/// Produces a random AST for a valid minilisp program.
pub fn random_ast() -> Expression {
    random_expr(Context {
        value_type_idents: HashMap::new(),
        ident_value_types: HashMap::new(),
        depth: 0,
    })
}

fn random_expr(context: Context) -> Expression {
    if context.depth > MAX_DEPTH {
        random_number(context.deeper())
    } else {
        let mut random_num = random_range(0..10);
        if random_num >= 4
            && let Some(ident) = context.random_ident()
        {
            return Expression::Identifier(ident.to_string());
        }
        random_num = random_range(0..4);

        match random_num {
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

fn random_null(context: Context) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 3 {
        if let Some(ident) = context.random_with_type(&ValueType::Null) {
            return Expression::Identifier(ident.to_string());
        }
        random_num = random_range(0..3);
    }

    if context.depth > MAX_DEPTH {
        Expression::Null
    } else {
        match random_num {
            0 => Expression::Null,
            1 => random_paren_expr(context.deeper(), &ValueType::Null),
            2 => random_expr(context.deeper()),
            _ => unreachable!(),
        }
    }
}

fn random_number(context: Context) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 2 {
        if let Some(ident) = context.random_with_type(&ValueType::Number) {
            return Expression::Identifier(ident.to_string());
        }
        random_num = random_range(0..2);
    }

    if context.depth > MAX_DEPTH {
        Expression::Number(random_range(0..100) as isize)
    } else {
        match random_num {
            0 => Expression::Number(random_range(0..100) as isize),
            1 => random_paren_expr(context.deeper(), &ValueType::Number),
            _ => unreachable!(),
        }
    }
}

fn random_cons(mut context: Context, target_type: &(ValueType, ValueType)) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 2 {
        if let Some(ident) = context.random_with_type(&ValueType::Cons((
            Box::new(target_type.0.clone()),
            Box::new(target_type.1.clone()),
        ))) {
            return Expression::Identifier(ident.to_string());
        }
        random_num = random_range(0..2);
    }

    context = context.deeper();
    match random_num {
        0 => *boxparexpr!(ParenExpression::Cons {
            car: Box::new(target_type.0.random_expr_fn()(context.clone())),
            cdr: Box::new(target_type.1.random_expr_fn()(context))
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

fn random_bool(context: Context) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 2 {
        if let Some(boolean) = context.random_with_type(&ValueType::Boolean) {
            return Expression::Identifier(boolean.to_string());
        }
        random_num = random_range(0..2);
    }

    match random_num {
        0 => random_number(context.deeper()),
        1 => random_null(context.deeper()),
        _ => unreachable!(),
    }
}

fn random_lambda(context: Context, target_type: ValueType) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 2 {
        if let Some(lambda) =
            context.random_with_type(&ValueType::Lambda(Box::new(target_type.clone())))
        {
            return Expression::Identifier(lambda.to_string());
        }
        random_num = random_range(0..2);
    }

    match random_num {
        0 => *boxparexpr!(ParenExpression::Lambda {
            arg: random_string(),
            body: Box::new(target_type.random_expr_fn()(context.deeper()))
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
        Expression::Paren(Box::new(ParenExpression::$op_variant {
            first: Box::new(random_number($context.clone())),
            second: Box::new(random_number($context)),
        }))
    };
}

// TODO maybe make context shared reference, just remove binding after subexpr complete
fn random_paren_expr(mut context: Context, target_type: &ValueType) -> Expression {
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
        6 => Expression::Paren(Box::new(ParenExpression::LogicalAnd {
            first: Box::new(random_bool(context.clone())),
            second: Box::new(random_bool(context)),
        })),
        7 => random_two_arg_parexpr!(LogicalOr, context),
        8 => Expression::Paren(Box::new(ParenExpression::LogicalNot {
            value: Box::new(random_bool(context)),
        })),
        9 => Expression::Paren(Box::new(ParenExpression::NullCheck {
            value: Box::new(random_null(context)),
        })),
        // any type
        10 => Expression::Paren(Box::new(ParenExpression::Condition {
            predicate: Box::new(random_bool(context.clone())),
            yes: Box::new(random_target(context.clone())),
            no: Box::new(random_target(context)),
        })),
        11 => {
            let ident = random_string();
            let value_expr = random_target(context.clone());
            context.bind(ident.clone(), target_type.clone());

            Expression::Paren(Box::new(ParenExpression::Binding {
                name: ident,
                value: Box::new(value_expr),
                body: Box::new(random_target(context)),
            }))
        }
        12 => Expression::Paren(Box::new(ParenExpression::Car {
            cons: boxparexpr!(ParenExpression::Cons {
                car: Box::new(random_target(context.clone())),
                cdr: Box::new(random_expr(context))
            }),
        })),
        13 => Expression::Paren(Box::new(ParenExpression::Cdr {
            cons: boxparexpr!(ParenExpression::Cons {
                car: Box::new(random_target(context.clone())),
                cdr: Box::new(random_expr(context))
            }),
        })),
        14 => Expression::Paren(Box::new(ParenExpression::Application {
            lambda: Box::new(random_lambda(context.clone(), target_type.clone())),
            argument: Box::new(random_target(context)),
        })),
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
