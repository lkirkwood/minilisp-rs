use std::{
    collections::HashMap,
    fmt::{Debug, Pointer},
    rc::Rc,
};

use anyhow::{Result, bail};

use crate::ast::{BoxExpr, Expression, ParenExpression};

#[derive(Clone)]
pub struct Lambda {
    name: String,
    func: Rc<dyn Fn(HashMap<String, Value>) -> Result<Value>>,
}

impl Debug for Lambda {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Lambda named {} with function pointer: ", self.name,)?;
        self.func.fmt(f)
    }
}

impl PartialEq for Lambda {
    fn eq(&self, other: &Self) -> bool {
        other.name == self.name
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Null,
    Number(usize),
    Cons((Box<Value>, Box<Value>)),
    Lambda(Lambda),
}

pub fn interpret(expr: BoxExpr) -> Result<Value> {
    recurse(expr, HashMap::new())
}

#[allow(clippy::boxed_local, clippy::too_many_lines)]
fn recurse(expr: BoxExpr, mut idents: HashMap<String, Value>) -> Result<Value> {
    match *expr {
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
        Expression::Paren(parexpr) => {
            match *parexpr {
                ParenExpression::Plus { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(first_num + second_num))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use + on a null value."
                        )
                    }
                }
                ParenExpression::Minus { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(first_num - second_num))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use − on a null value."
                        )
                    }
                }
                ParenExpression::Times { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(first_num * second_num))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use × on a null value."
                        )
                    }
                }
                ParenExpression::Equals { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(usize::from(first_num == second_num)))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use = on a null value."
                        )
                    }
                }
                ParenExpression::Condition { predicate, yes, no } => {
                    match recurse(predicate, idents.clone())? {
                        Value::Number(num) => {
                            if num > 0 {
                                recurse(yes, idents)
                            } else {
                                recurse(no, idents)
                            }
                        }
                        Value::Cons(_) => recurse(yes, idents), // TODO decide on correct behaviour here
                        Value::Null => recurse(no, idents),
                        Value::Lambda(_) => bail!(
                            "The program must be invalid, because you can't use a lambda \
                         as the predicate for a conditional."
                        ),
                    }
                }
                ParenExpression::Lambda { name, body } => Ok(Value::Lambda(Lambda {
                    name: name.clone(),
                    func: Rc::new(move |idents| recurse(body.clone(), idents)),
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
                    if let Value::Cons(cons_cell) = cons_val {
                        Ok(*cons_cell.0)
                    } else {
                        bail!(
                            "The program must be invalid, because \"car\" only works on \
                         cons cells, not {cons_val:?}"
                        )
                    }
                }
                ParenExpression::Cdr { cons } => {
                    let cons_val = recurse(cons, idents)?;
                    if let Value::Cons(cons_cell) = cons_val {
                        Ok(*cons_cell.1)
                    } else {
                        bail!(
                            "The program must be invalid, because \"cdr\" only works on \
                         cons cells, not {cons_val:?}"
                        )
                    }
                }
                ParenExpression::NullCheck { value } => {
                    if let Value::Null = recurse(value, idents)? {
                        Ok(Value::Number(1))
                    } else {
                        Ok(Value::Number(0))
                    }
                }
                ParenExpression::LessThan { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(usize::from(first_num < second_num)))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use \
                         ‹ on a non-numeric value."
                        )
                    }
                }
                ParenExpression::GreaterThan { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(usize::from(first_num > second_num)))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use \
                         › on a non-numeric value."
                        )
                    }
                }
                ParenExpression::LogicalAnd { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(usize::from(
                            first_num != 0 && second_num != 0,
                        )))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use \
                         ∧ on a non-numeric value."
                        )
                    }
                }
                ParenExpression::LogicalOr { first, second } => {
                    if let Value::Number(first_num) = recurse(first, idents.clone())?
                        && let Value::Number(second_num) = recurse(second, idents)?
                    {
                        Ok(Value::Number(usize::from(
                            first_num != 0 || second_num != 0,
                        )))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use \
                         ∨ on a non-numeric value."
                        )
                    }
                }
                ParenExpression::LogicalNot { value } => {
                    if let Value::Number(value_num) = recurse(value, idents.clone())? {
                        Ok(Value::Number(usize::from(value_num == 0)))
                    } else {
                        bail!(
                            "The program must be invalid, because you can't use \
                           ¬ on a non-numeric value."
                        )
                    }
                }
                ParenExpression::Match { value, patterns } => todo!("interpret match statement"),
                ParenExpression::Exprs { exprs } => {
                    let mut expr_iter = exprs.into_iter();
                    // TODO decide if variadic forms are even needed - lambdas only take one arg!
                    if let Some(first_expr) = expr_iter.next()
                        && let Value::Lambda(lambda) = recurse(first_expr, idents.clone())?
                        && let Some(arg) = expr_iter.next()
                    {
                        idents.insert(lambda.name, recurse(arg, idents.clone())?);
                        (lambda.func)(idents)
                    } else {
                        bail!(
                            "The program must be invalid, because lambda application was used \
                         on a non-lambda value or with too few arguments."
                        )
                    }
                }
            }
        }
        Expression::PatternClause(patt_clause) => todo!("Interpret pattern clause"),
        Expression::Wildcard => todo!("Interpret wildcard expr"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::parser::parse;
    use crate::tokeniser::tokenise;

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
    fn interpret_lambda() {
        assert_eq!(interpret_str("((λ x (+ x 1)) 5)"), Value::Number(6))
    }

    #[test]
    fn interpret_binding() {
        assert_eq!(interpret_str("(≜ x 10 (+ x x))"), Value::Number(20));
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
}
