use std::collections::{HashMap, HashSet, hash_map::Entry};

// TODO remove this for something lighter
use rand::random_range;

use crate::ast::{Expression, ParenExpression};

const MAX_DEPTH: usize = 10;

/// Represents the different types of value an expression can evaluate to.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum ValueType {
    Null,
    Number,
    Cons((Box<ValueType>, Box<ValueType>)),
    Lambda(Box<ValueType>),
}

impl ValueType {
    /// Returns a random instance of `ValueType`.
    fn random() -> Self {
        match random_range(0..4) {
            0 => Self::Null,
            1 => Self::Number,
            2 => Self::Cons((
                Box::new(ValueType::random()),
                (Box::new(ValueType::random())),
            )),
            3 => Self::Lambda(Box::new(ValueType::random())),
            _ => unreachable!(),
        }
    }

    /// Returns a pointer to a function which, when called, will produce a random
    /// expression of this value type.
    fn random_expr_fn(&self) -> Box<dyn Fn(&mut Context) -> Expression + '_> {
        match self {
            ValueType::Null => Box::new(random_null) as Box<dyn Fn(&mut Context) -> Expression>,
            ValueType::Number => Box::new(random_number) as Box<dyn Fn(&mut Context) -> Expression>,
            ValueType::Cons((car_target, cdr_target)) => Box::new(|context: &mut Context| {
                random_cons(context, &(*car_target.clone(), *cdr_target.clone()))
            })
                as Box<dyn Fn(&mut Context) -> Expression>,
            ValueType::Lambda(target_type) => {
                Box::new(|context: &mut Context| random_lambda(context, *target_type.clone()))
                    as Box<dyn Fn(&mut Context) -> Expression>
            }
        }
    }
}

#[derive(Clone)]
struct Context {
    ident_value_types: HashMap<String, ValueType>,
    value_type_idents: HashMap<ValueType, HashSet<String>>,
    depth: usize,
}

impl Context {
    /// Bind an identifier to the given `ValueType`.
    fn bind(&mut self, ident: String, value_type: ValueType) {
        self.ident_value_types
            .insert(ident.clone(), value_type.clone());

        match self.value_type_idents.entry(value_type) {
            Entry::Vacant(entry) => {
                entry.insert(HashSet::from([ident]));
            }
            Entry::Occupied(mut entry) => {
                entry.get_mut().insert(ident);
            }
        }
    }

    /// Unbind an identifier.
    fn unbind(&mut self, ident: &str) {
        let Some(value_type) = self.ident_value_types.remove(ident) else {
            panic!("Tried to unbind an unbound identifier {ident}.");
        };

        let Some(idents) = self.value_type_idents.get_mut(&value_type) else {
            panic!(
                "While unbinding ident, there were no idents for the value type. {ident}, {value_type:?}"
            );
        };

        idents.remove(ident);
    }

    /// Return any random identifier.
    fn random_ident(&self) -> Option<&str> {
        let nonempty_vtypes: Vec<_> = self
            .value_type_idents
            .iter()
            .filter(|(_, idents)| !idents.is_empty())
            .collect();

        if nonempty_vtypes.is_empty() {
            return None;
        }

        let (_, random_idents) = nonempty_vtypes[random_range(0..nonempty_vtypes.len())];
        let random_idx = random_range(0..random_idents.len());
        for (idx, ident) in random_idents.iter().enumerate() {
            if idx == random_idx {
                return Some(ident);
            }
        }

        panic!("Failed to choose a random identifier even though there were some to choose from.")
    }

    /// Return a random identifier with the given `ValueType`.
    fn random_with_type(&self, value_type: &ValueType) -> Option<&str> {
        if let Some(idents) = self.value_type_idents.get(value_type)
            && !idents.is_empty()
        {
            let random_idx = random_range(0..idents.len());
            for (idx, ident) in idents.iter().enumerate() {
                if idx == random_idx {
                    return Some(ident);
                }
            }

            panic!(
                "Failed to choose a random identifier even though there were some to choose from."
            )
        } else {
            None
        }
    }

    /// Return the mutable reference to `Context` with an increased depth.
    fn deeper(&mut self) -> &mut Self {
        self.depth += 1;
        self
    }

    /// Return the mutable reference to `Context` with an decreeased depth.
    fn shallower(&mut self) -> &mut Self {
        self.depth -= 1;
        self
    }
}

/// Produces a random, valid minilisp program.
pub fn random_program() -> String {
    random_ast().into()
}

/// Produces a random AST for a valid minilisp program.
pub fn random_ast() -> Expression {
    let mut context = Context {
        value_type_idents: HashMap::new(),
        ident_value_types: HashMap::new(),
        depth: 1,
    };

    let ast = match random_range(0..3) {
        0 => random_null(&mut context),
        1 => random_number(&mut context),
        2 => random_cons(&mut context, &(ValueType::random(), ValueType::random())),
        _ => unreachable!(),
    };

    assert_eq!(context.depth, 1);
    ast
}

fn random_expr(context: &mut Context) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 4
        && let Some(ident) = context.random_ident()
    {
        return Expression::Identifier(ident.to_string());
    }

    if context.depth > MAX_DEPTH {
        random_num = random_range(0..2);
    } else {
        random_num = random_range(0..4);
    }

    let expr = match random_num {
        0 => random_null(context.deeper()),
        1 => random_number(context.deeper()),
        2 => random_cons(
            context.deeper(),
            &(ValueType::random(), ValueType::random()),
        ),
        3 => random_lambda(context.deeper(), ValueType::random()),
        _ => unreachable!(),
    };

    context.shallower();
    expr
}

fn random_null(context: &mut Context) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 3 {
        if let Some(ident) = context.random_with_type(&ValueType::Null) {
            return Expression::Identifier(ident.to_string());
        }
        random_num = random_range(0..3);
    }

    if context.depth > MAX_DEPTH {
        random_num = 0;
    }

    context.deeper();
    let nullable = match random_num {
        0 => Expression::Null,
        1 => random_paren_expr(context, &ValueType::Null),
        2 => random_expr(context),
        _ => unreachable!(),
    };

    context.shallower();
    nullable
}

fn random_number(context: &mut Context) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 2 {
        if let Some(ident) = context.random_with_type(&ValueType::Number) {
            return Expression::Identifier(ident.to_string());
        }
        random_num = random_range(0..2);
    }

    if context.depth > MAX_DEPTH {
        random_num = 0;
    }

    context.deeper();
    let number = match random_num {
        0 => Expression::Number(random_range(0..100)),
        1 => random_paren_expr(context, &ValueType::Number),
        _ => unreachable!(),
    };

    context.shallower();
    number
}

fn random_cons(context: &mut Context, target_type: &(ValueType, ValueType)) -> Expression {
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

    context.deeper();
    let cons = match random_num {
        0 => *boxparexpr!(ParenExpression::Cons {
            car: Box::new(target_type.0.random_expr_fn()(context)),
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
    };

    context.shallower();
    cons
}

fn random_lambda(context: &mut Context, target_type: ValueType) -> Expression {
    let mut random_num = random_range(0..10);
    if random_num >= 2 {
        if let Some(lambda) =
            context.random_with_type(&ValueType::Lambda(Box::new(target_type.clone())))
        {
            return Expression::Identifier(lambda.to_string());
        }
        random_num = random_range(0..2);
    }

    if context.depth > MAX_DEPTH {
        random_num = 0;
    }

    context.deeper();
    let lambda = match random_num {
        0 => *boxparexpr!(ParenExpression::Lambda {
            arg: random_string(),
            body: Box::new(target_type.random_expr_fn()(context))
        }),
        1 => random_paren_expr(context, &ValueType::Lambda(Box::new(target_type))),
        _ => unreachable!(),
    };

    context.shallower();
    lambda
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
            first: Box::new(random_number($context)),
            second: Box::new(random_number($context)),
        }))
    };
}

// TODO maybe make context shared reference, just remove binding after subexpr complete
fn random_paren_expr(context: &mut Context, target_type: &ValueType) -> Expression {
    let random_target = target_type.random_expr_fn();
    context.deeper();

    let range = if matches!(target_type, ValueType::Null | ValueType::Number) {
        if context.depth > MAX_DEPTH {
            0..10
        } else {
            0..20
        }
    } else {
        10..20
    };

    let paren_expr = match random_range(range) {
        // number
        0 => random_two_arg_parexpr!(Plus, context),
        1 => random_two_arg_parexpr!(Monus, context),
        2 => random_two_arg_parexpr!(Times, context),
        3 => random_two_arg_parexpr!(Equals, context),
        4 => random_two_arg_parexpr!(LessThan, context),
        5 => random_two_arg_parexpr!(GreaterThan, context),
        6 => random_two_arg_parexpr!(LogicalAnd, context),
        7 => random_two_arg_parexpr!(LogicalOr, context),
        8 => Expression::Paren(Box::new(ParenExpression::LogicalNot {
            value: Box::new(random_number(context)),
        })),
        9 => Expression::Paren(Box::new(ParenExpression::NullCheck {
            value: Box::new(random_null(context)),
        })),
        // any type
        10 => Expression::Paren(Box::new(ParenExpression::Condition {
            predicate: Box::new(random_number(context)),
            yes: Box::new(random_target(context)),
            no: Box::new(random_target(context)),
        })),
        11 => {
            let ident = random_string();
            let value_expr = random_target(context);
            context.bind(ident.clone(), target_type.clone());

            let binding_expr = Expression::Paren(Box::new(ParenExpression::Binding {
                name: ident.clone(),
                value: Box::new(value_expr),
                body: Box::new(random_target(context)),
            }));

            context.unbind(&ident);
            binding_expr
        }
        12 => Expression::Paren(Box::new(ParenExpression::Car {
            cons: boxparexpr!(ParenExpression::Cons {
                car: Box::new(random_target(context)),
                cdr: Box::new(random_expr(context))
            }),
        })),
        13 => Expression::Paren(Box::new(ParenExpression::Cdr {
            cons: boxparexpr!(ParenExpression::Cons {
                car: Box::new(random_expr(context)),
                cdr: Box::new(random_target(context))
            }),
        })),
        14..20 => Expression::Paren(Box::new(ParenExpression::Application {
            lambda: Box::new(random_lambda(context, target_type.clone())),
            argument: Box::new(random_target(context)),
        })),
        _ => unreachable!(),
    };

    context.shallower();
    paren_expr
}

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::{
        interpreter::interpret, parser::parse, randprog::random_program, tokeniser::tokenise,
    };

    #[test]
    fn test_random_program() {
        let program = random_program();
        fs::write("/tmp/lastprog", &program).unwrap();
        let result = interpret(parse(tokenise(&program).unwrap()).unwrap()).unwrap();
        println!("{result}");
    }
}
