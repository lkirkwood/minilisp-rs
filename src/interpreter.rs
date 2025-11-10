use std::{
    collections::HashMap,
    fmt::{Display, Pointer},
    rc::Rc,
};

use anyhow::{Result, bail};

use crate::ast::{BoxExpr, Expression, ParenExpression, Pattern, PatternClause};

#[derive(Clone)]
pub struct Lambda {
    arg: String,
    func: Rc<dyn Fn(Value) -> Result<Value>>,
}

impl Lambda {
    fn call(self, value: Value) -> Result<Value> {
        (self.func)(value)
    }
}

#[derive(Clone)]
pub enum Value {
    Null,
    Number(usize),
    Cons((Box<Value>, Box<Value>)),
    Lambda(Lambda),
    Application(Rc<dyn Fn() -> Result<Value>>),
}

impl Value {
    /// Tries to interpret the value as a boolean, performing lazy evaluation if necessary.
    fn truthy(self) -> Result<bool> {
        match self {
            Self::Number(num) => Ok(num > 0),
            Self::Null => Ok(false),
            Self::Application(func) => (func)()?.truthy(),
            Self::Lambda(_) | Self::Cons(_) => bail!(
                "The program must be invalid, because you can't use a lambda \
                or a cons cell as the predicate for a conditional."
            ),
        }
    }

    fn eval(mut self) -> Result<Self> {
        while let Self::Application(func) = self {
            self = (func)()?;
        }
        Ok(self)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Null => write!(f, "∅"),
            Self::Number(num) => write!(f, "{num}"),
            Self::Cons((val0, val1)) => write!(f, "({val0} {val1})"),
            Self::Lambda(Lambda { arg, func }) => {
                write!(f, "(λ \"{arg}\" - ")?;
                func.fmt(f)?;
                write!(f, ")")
            }
            Self::Application(func) => {
                write!(f, "Lambda application of function at: ")?;
                func.fmt(f)
            }
        }
    }
}

enum PatternMatch {
    None,
    Simple,
    Binding(HashMap<String, Value>),
}

impl Value {
    /// Returns a
    fn matches(&self, pattern: &Pattern) -> PatternMatch {
        match pattern {
            Pattern::Wildcard => PatternMatch::Simple,
            Pattern::Identifier(ident) => {
                PatternMatch::Binding(HashMap::from([(ident.clone(), self.clone())]))
            }
            Pattern::Null => {
                if let Self::Null = self {
                    PatternMatch::Simple
                } else {
                    PatternMatch::None
                }
            }
            Pattern::Number(their_num) => {
                if let Self::Number(our_num) = self
                    && our_num == their_num
                {
                    PatternMatch::Simple
                } else {
                    PatternMatch::None
                }
            }
            Pattern::Cons((pattern0, pattern1)) => {
                if let Value::Cons((value0, value1)) = self {
                    let mut bindings = HashMap::new();

                    match value0.matches(pattern0) {
                        PatternMatch::Binding(bindings0) => bindings.extend(bindings0),
                        PatternMatch::Simple => {}
                        PatternMatch::None => return PatternMatch::None,
                    }

                    match value1.matches(pattern1) {
                        PatternMatch::Binding(bindings1) => bindings.extend(bindings1),
                        PatternMatch::Simple => {}
                        PatternMatch::None => return PatternMatch::None,
                    }

                    if bindings.is_empty() {
                        PatternMatch::Simple
                    } else {
                        PatternMatch::Binding(bindings)
                    }
                } else {
                    PatternMatch::None
                }
            }
        }
    }
}

pub fn interpret(expr: BoxExpr) -> Result<Value> {
    recurse(expr, HashMap::new())?.eval()
}

fn two_arg_numeric_op(
    first: BoxExpr,
    second: BoxExpr,
    idents: HashMap<String, Value>,
    op: Box<dyn Fn(usize, usize) -> usize>,
    op_char: char,
) -> Result<Value> {
    let first_val = recurse(first, idents.clone())?;
    let second_val = recurse(second, idents)?;
    Ok(Value::Application(Rc::new(move || {
        if let Value::Number(first_num) = first_val.clone().eval()?
            && let Value::Number(second_num) = second_val.clone().eval()?
        {
            Ok(Value::Number((op)(first_num, second_num)))
        } else {
            bail!(
                "The program must be invalid, because you can't use {op_char} \
                    on non-numeric values.",
            )
        }
    })))
}

#[allow(clippy::boxed_local)]
fn recurse(expr: BoxExpr, mut idents: HashMap<String, Value>) -> Result<Value> {
    match *expr {
        Expression::Paren(parexpr) => recurse_parexpr(*parexpr, idents),
        Expression::Null => Ok(Value::Null),
        Expression::Number(num) => Ok(Value::Number(num)),
        Expression::Identifier(ref ident) => {
            if let Some(val) = idents.get(ident) {
                Ok(val.clone())
            } else {
                bail!(
                    "The program must be invalid, because an unbound identifier \
                     \"{ident}\" was used."
                )
            }
        }
        Expression::PatternClause(patt_clause) => {
            let PatternClause { pattern, body } = *patt_clause;
            match idents.get("_match") {
                Some(matchval) => match matchval.matches(&pattern) {
                    PatternMatch::None => Ok(Value::Null),
                    PatternMatch::Simple => recurse(body, idents),
                    PatternMatch::Binding(bindings) => {
                        idents.extend(bindings);
                        recurse(body, idents)
                    }
                },
                None => bail!(
                    "Something went wrong internally; matching a pattern clause \
                    without any _match ident."
                ),
            }
        }
        Expression::Wildcard => bail!(
            "The program must be invalid, because a wildcard character \
            `_` can only be present as a pattern in a match statement."
        ),
    }
}

#[allow(clippy::too_many_lines)]
fn recurse_parexpr(parexpr: ParenExpression, mut idents: HashMap<String, Value>) -> Result<Value> {
    match parexpr {
        ParenExpression::Plus { first, second } => {
            two_arg_numeric_op(first, second, idents, Box::new(|n0, n1| n0 + n1), '+')
        }
        ParenExpression::Minus { first, second } => {
            two_arg_numeric_op(first, second, idents, Box::new(|n0, n1| n0 - n1), '−')
        }
        ParenExpression::Times { first, second } => {
            two_arg_numeric_op(first, second, idents, Box::new(|n0, n1| n0 * n1), '×')
        }
        ParenExpression::Equals { first, second } => two_arg_numeric_op(
            first,
            second,
            idents,
            Box::new(|n0, n1| usize::from(n0 == n1)),
            '=',
        ),
        ParenExpression::Condition { predicate, yes, no } => {
            if recurse(predicate, idents.clone())?.truthy()? {
                recurse(yes, idents)
            } else {
                recurse(no, idents)
            }
        }
        ParenExpression::Lambda { arg, body } => Ok(Value::Lambda(Lambda {
            arg: arg.clone(),
            func: Rc::new(move |value| {
                let mut local_idents = idents.clone();
                local_idents.insert(arg.clone(), value);
                recurse(body.clone(), local_idents)
            }),
        })),
        ParenExpression::Binding { name, value, body } => {
            idents.insert(name.clone(), recurse(value, idents.clone())?);
            recurse(body, idents)
        }
        ParenExpression::Cons { car, cdr } => Ok(Value::Cons((
            Box::new(recurse(car, idents.clone())?),
            Box::new(recurse(cdr, idents)?),
        ))),
        ParenExpression::Car { cons } => {
            let cons_val = recurse(cons, idents)?;
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
        ParenExpression::Cdr { cons } => {
            let cons_val = recurse(cons, idents)?;
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
        ParenExpression::NullCheck { value } => {
            let value = recurse(value, idents)?;
            Ok(Value::Application(Rc::new(move || {
                if let Value::Null = value.clone().eval()? {
                    Ok(Value::Number(1))
                } else {
                    Ok(Value::Number(0))
                }
            })))
        }
        ParenExpression::LessThan { first, second } => two_arg_numeric_op(
            first,
            second,
            idents,
            Box::new(|n0, n1| usize::from(n0 < n1)),
            '‹',
        ),
        ParenExpression::GreaterThan { first, second } => two_arg_numeric_op(
            first,
            second,
            idents,
            Box::new(|n0, n1| usize::from(n0 > n1)),
            '›',
        ),
        ParenExpression::LogicalAnd { first, second } => two_arg_numeric_op(
            first,
            second,
            idents,
            Box::new(|n0, n1| usize::from(n0 != 0 && n1 != 0)),
            '∧',
        ),
        ParenExpression::LogicalOr { first, second } => two_arg_numeric_op(
            first,
            second,
            idents,
            Box::new(|n0, n1| usize::from(n0 != 0 || n1 != 0)),
            '∨',
        ),
        ParenExpression::LogicalNot { value } => {
            let value = recurse(value, idents.clone())?;
            Ok(Value::Application(Rc::new(move || {
                if let Value::Number(value_num) = value.clone().eval()? {
                    Ok(Value::Number(usize::from(value_num == 0)))
                } else {
                    bail!(
                        "The program must be invalid, because you can't use \
                                ¬ on a non-numeric value."
                    )
                }
            })))
        }
        ParenExpression::Match { value, patterns } => {
            idents.insert("_match".to_string(), recurse(value, idents.clone())?); // Underscores are reserved characters
            let mut pattern_values = Vec::new();
            for pattern in patterns {
                pattern_values.push(recurse(
                    Box::new(Expression::PatternClause(pattern)),
                    idents.clone(),
                )?);
            }

            Ok(Value::Application(Rc::new(move || {
                let mut found = Value::Null;
                for pattern in pattern_values.clone() {
                    match pattern.eval()? {
                        Value::Null => {}
                        other => found = other,
                    }
                }
                Ok(found)
            })))
        }
        // TODO decide if variadic forms are even needed - lambdas only take one arg!
        ParenExpression::Exprs { exprs } => {
            let mut expr_iter = exprs.clone().into_iter();
            let first_expr = expr_iter.next();
            if first_expr.is_none() {
                bail!(
                    "The program must be invalid, because lambda application was used \
                         on an empty list of terms - it should look like `()`."
                )
            }
            let applicant = recurse(first_expr.unwrap(), idents.clone())?;

            let arg_expr = expr_iter.next();
            if arg_expr.is_none() {
                bail!(
                    "The program must be invalid, because lambda application was used \
                         without any arguments - it should look like `(<one term>)`."
                )
            }
            let arg = recurse(arg_expr.unwrap(), idents)?;

            if let Value::Lambda(lambda) = applicant {
                Ok(Value::Application(Rc::new(move || {
                    lambda.clone().call(arg.clone())
                })))
            } else if let Value::Application(_) = applicant {
                Ok(Value::Application(Rc::new(move || {
                    let evaluated = applicant.clone().eval()?;
                    if let Value::Lambda(lambda) = evaluated {
                        lambda.call(arg.clone())
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
                         on something that was not a lambda - instead it was: {applicant}"
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;

    use super::*;

    use crate::parser::parse;
    use crate::tokeniser::tokenise;

    impl PartialEq for Lambda {
        fn eq(&self, other: &Self) -> bool {
            other.arg == self.arg
        }
    }

    impl PartialEq for Value {
        fn eq(&self, other: &Self) -> bool {
            match self {
                Self::Null => {
                    if let Self::Null = other {
                        true
                    } else {
                        false
                    }
                }
                Self::Number(num) => {
                    if let Self::Number(other_num) = other {
                        other_num == num
                    } else {
                        false
                    }
                }
                Self::Cons((value0, value1)) => {
                    if let Self::Cons((other0, other1)) = other {
                        other0 == value0 && other1 == value1
                    } else {
                        false
                    }
                }
                Self::Lambda(lambda) => {
                    if let Self::Lambda(other_lambda) = other {
                        other_lambda.arg == lambda.arg
                    } else {
                        false
                    }
                }
                Self::Application(func) => {
                    if let Self::Application(other_func) = other {
                        match ((func)(), (other_func)()) {
                            (Ok(value), Ok(other_value)) => value == other_value,
                            (Err(err), Err(other_err)) => err.to_string() == other_err.to_string(),
                            _ => false,
                        }
                    } else {
                        false
                    }
                }
            }
        }
    }

    impl Debug for Value {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{self}")
        }
    }

    fn interpret_str(prog: &str) -> Value {
        interpret(parse(tokenise(prog).unwrap()).unwrap()).unwrap()
    }

    #[test]
    fn interpret_number() {
        assert_eq!(interpret_str("42"), Value::Number(42));
    }

    #[test]
    fn interpret_addition() {
        assert_eq!(interpret_str("(+ 123 456)"), Value::Number(579));
    }

    #[test]
    fn interpret_arithmetic() {
        assert_eq!(interpret_str("(+ (× 1 42) (− 42 0))"), Value::Number(84));
    }

    #[test]
    fn interpret_conditional() {
        assert_eq!(interpret_str("(? (= 1 1) 10 20)"), Value::Number(10));
    }

    #[test]
    fn interpret_lambda_immediate() {
        assert_eq!(interpret_str("((λ x (+ x 1)) 5)"), Value::Number(6))
    }

    #[test]
    fn interpret_lambda_bound() {
        assert_eq!(
            interpret_str("(≜ add-one (λ x (+ x 1)) (add-one 5))"),
            Value::Number(6)
        )
    }

    #[test]
    fn interpret_binding() {
        assert_eq!(interpret_str("(≜ x 10 (+ x x))"), Value::Number(20));
    }

    #[test]
    fn interpret_unbound_ident() {
        assert!(interpret(parse(tokenise("(⌒)").unwrap()).unwrap()).is_err());
    }

    #[test]
    fn interpret_less_than() {
        assert_eq!(interpret_str("(≜ x 10 (‹ x (+ x 1)))"), Value::Number(1));
    }

    #[test]
    fn interpret_greater_than() {
        assert_eq!(interpret_str("(≜ x 10 (› x (+ x 1)))"), Value::Number(0));
    }

    #[test]
    fn interpret_logic_1() {
        assert_eq!(interpret_str("(∧ 1 (∨ 0 (¬ 0)))"), Value::Number(1));
    }

    #[test]
    fn interpret_logic_2() {
        assert_eq!(interpret_str("(∧ 1 (∨ 0 (¬ 1)))"), Value::Number(0));
    }

    #[test]
    fn interpret_logic_3() {
        assert_eq!(interpret_str("(∧ 1 (∨ 1 (¬ 1)))"), Value::Number(1));
    }

    #[test]
    fn interpret_logic_4() {
        assert_eq!(interpret_str("(∧ 0 (∨ 1 (¬ 1)))"), Value::Number(0));
    }

    #[test]
    fn interpret_lists() {
        assert_eq!(
            interpret_str("(≜ lst (∷ 42 (∷ 99 ∅)) (∨ (∘ (← lst)) (∘ (→ (→ lst)))))"),
            Value::Number(1)
        );
    }

    #[test]
    fn interpret_match() {
        assert_eq!(
            interpret_str(
                "(⊢ 42
                    (42 1)
                    (99 0))"
            ),
            Value::Number(1)
        )
    }

    #[test]
    fn interpret_match_cons() {
        assert_eq!(
            interpret_str(
                "(⊢ (∷ 42 99)
                    (∅ 0)
                    ((∷ x _) x))"
            ),
            Value::Number(42)
        )
    }

    #[test]
    fn interpret_match_cons_concrete() {
        assert_eq!(
            interpret_str(
                "(⊢ (∷ 42 (∷ 43 (∷ 44 ∅)))
                    (∅ 0)
                    ((∷ 42 (∷ 43 (∷ 44 ∅))) 1))"
            ),
            Value::Number(1)
        )
    }

    #[test]
    fn interpret_match_cons_partial_concrete_1() {
        assert_eq!(
            interpret_str(
                "(⊢ (∷ 42 (∷ 43 (∷ 44 ∅)))
                    (∅ 0)
                    ((∷ 42 (∷ 43 x)) x))"
            ),
            Value::Cons((Box::new(Value::Number(44)), Box::new(Value::Null)))
        )
    }

    #[test]
    fn interpret_match_cons_partial_concrete_2() {
        assert_eq!(
            interpret_str(
                "(⊢ (∷ 42 (∷ 43 (∷ 44 ∅)))
                    (∅ 0)
                    ((∷ 42 (∷ x (∷ 44 ∅))) x))"
            ),
            Value::Number(43)
        )
    }

    #[test]
    fn interpret_match_complex_1() {
        assert_eq!(
            interpret_str(
                "(≜ first-or-default
                    (λ lst (⊢ lst
                        (∅ 0)
                        ((∷ x _) x)))
                    (first-or-default (∷ 42 ∅)))"
            ),
            Value::Number(42)
        )
    }

    #[test]
    fn interpret_match_complex_2() {
        assert_eq!(
            interpret_str(
                "(≜ first-or-default
                    (λ lst (⊢ lst
                        (∅ 0)
                        ((∷ _ y) y)))
                    (first-or-default (∷ 42 ∅)))"
            ),
            Value::Null
        )
    }

    #[test]
    fn interpret_match_complex_3() {
        assert_eq!(
            interpret_str(
                "(≜ first-or-default
                    (λ lst (⊢ lst
                        (∅ 0)
                        ((∷ x y) (+ x y))))
                    (first-or-default (∷ 42 1)))"
            ),
            Value::Number(43)
        )
    }

    #[test]
    fn interpret_match_deep_nest() {
        assert_eq!(
            interpret_str(
                "(⊢ (∷ 42 (∷ 43 (∷ 44 (∷ 45 ∅))))
                    (∅ 0)
                    ((∷ a (∷ b (∷ c (∷ d ∅)))) c))"
            ),
            Value::Number(44)
        )
    }

    #[test]
    fn interpret_match_first_non_null() {
        // TODO decide if this behaviour is ok
        assert_eq!(
            interpret_str(
                "(⊢ 42
                    (42 ∅)
                    (_ 1))"
            ),
            Value::Number(1)
        )
    }

    #[test]
    fn interpret_currying() {
        assert_eq!(
            interpret_str(
                "(≜ times
                    (λ x
                        (λ y
                            (× x y)))
                    ((times 6) 7))"
            ),
            Value::Number(42)
        );
    }

    #[test]
    fn interpret_lazily() {
        assert_eq!(
            interpret_str(
                "(≜ Ω
                    ((λ x (x x)) (λ x (x x)))
                    ((λ x 1) Ω))"
            ),
            Value::Number(1)
        )
    }

    #[test]
    fn interpret_y_combinator() {
        assert_eq!(
            interpret_str(
                "(≜ Y
                    (λ f ((λ x (f (x x))) (λ x (f (x x)))))
                    ((Y (λ r (λ n (+ n 1)))) 5))"
            ),
            Value::Number(6)
        );
    }

    #[test]
    fn interpret_z_combinator() {
        assert_eq!(
            interpret_str(
                "(≜ Z
                    (λ f
                        ((λ x (f (λ v ((x x) v))))
                            (λ x (f (λ v ((x x) v))))))
                    (≜ G
                    (λ r (λ n (+ n 1)))
                    (≜ add-one
                        (Z G)
                        (add-one 1))))"
            ),
            Value::Number(2)
        );
    }

    #[test]
    fn interpret_factorial() {
        assert_eq!(
            interpret_str(
                "(≜ Y
                    (λ f ((λ x (f (x x))) (λ x (f (x x)))))
                    (≜ factorial
                        (Y (λ f
                            (λ n
                                (? (= n 0)
                                    1
                                    (× n (f (− n 1)))))))
                        (factorial 5)))"
            ),
            Value::Number(120)
        );
    }

    #[test]
    fn interpret_fibonacci() {
        assert_eq!(
            interpret_str(
                "(≜ Y
                    (λ f ((λ x (f (x x))) (λ x (f (x x)))))
                    (≜ fib
                        (Y (λ f
                            (λ n (? (= n 0)
                                0
                                (? (= n 1)
                                    1
                                    (+ (f (− n 1)) (f (− n 2))))))))
                        (fib 10)))"
            ),
            Value::Number(55)
        );
    }

    #[test]
    fn interpret_sum() {
        assert_eq!(
            interpret_str(
                "(≜ Y
                    (λ f ((λ x (f (x x))) (λ x (f (x x)))))
                    (≜ sum
                        (Y (λ f
                            (λ lst (⊢ lst
                                (∅ 0)
                                ((∷ car cdr) (+ car (f cdr)))))))
                        (sum (∷ 1 (∷ 2 (∷ 3 ∅))))))"
            ),
            Value::Number(6)
        );
    }

    #[test]
    fn interpret_list_length() {
        assert_eq!(
            interpret_str(
                "(≜ Y
                    (λ f ((λ x (f (x x))) (λ x (f (x x)))))
                    (≜ length
                        (Y (λ f (λ lst (? (∘ lst) 0 (+ 1 (f (→ lst)))))))
                        (length (∷ 1 (∷ 2 (∷ 3 ∅))))))"
            ),
            Value::Number(3)
        );
    }
}
