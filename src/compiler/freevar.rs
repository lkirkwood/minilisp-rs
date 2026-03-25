use std::collections::HashSet;

use crate::ast::{BoxExpr, Expression, ParenExpression};

/// Find the free variables referenced by the lambda.
pub fn lambda_free_vars<'a, 'b>(arg: &'a str, body: &'b BoxExpr) -> HashSet<&'b str> {
    let mut free_vars = expr_free_vars(body);
    free_vars.remove(arg);
    free_vars
}

fn expr_free_vars(expr: &BoxExpr) -> HashSet<&str> {
    let mut free_vars = HashSet::new();

    if let Expression::Identifier(ident) = &**expr {
        free_vars.insert(ident.as_str());
    } else if let Expression::Paren(parexpr) = &**expr {
        match &**parexpr {
            ParenExpression::Plus { first, second }
            | ParenExpression::Monus { first, second }
            | ParenExpression::Times { first, second }
            | ParenExpression::Equals { first, second }
            | ParenExpression::GreaterThan { first, second }
            | ParenExpression::LessThan { first, second }
            | ParenExpression::LogicalAnd { first, second }
            | ParenExpression::LogicalOr { first, second } => {
                free_vars.extend(expr_free_vars(first));
                free_vars.extend(expr_free_vars(second));
            }
            ParenExpression::Condition { predicate, yes, no } => {
                free_vars.extend(expr_free_vars(predicate));
                free_vars.extend(expr_free_vars(yes));
                free_vars.extend(expr_free_vars(no));
            }
            ParenExpression::Binding { name, body, .. } => {
                free_vars.extend(expr_free_vars(body));
                free_vars.remove(name.as_str());
            }
            ParenExpression::Cons { car, cdr } => {
                free_vars.extend(expr_free_vars(car));
                free_vars.extend(expr_free_vars(cdr));
            }
            ParenExpression::Car { cons } | ParenExpression::Cdr { cons } => {
                free_vars.extend(expr_free_vars(cons));
            }
            ParenExpression::NullCheck { value } | ParenExpression::LogicalNot { value } => {
                free_vars.extend(expr_free_vars(value));
            }
            ParenExpression::Application { lambda, argument } => {
                free_vars.extend(expr_free_vars(lambda));
                free_vars.extend(expr_free_vars(argument));
            }
            ParenExpression::Lambda { arg, body } => {
                free_vars.extend(lambda_free_vars(arg, body));
            }
        }
    }

    free_vars
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::ast::{Expression, ParenExpression};

    use super::lambda_free_vars;

    #[test]
    fn free_var_simple() {
        let body = Box::new(Expression::Identifier("foo".to_string()));
        let free_vars = lambda_free_vars("", &body);
        assert_eq!(free_vars, HashSet::from(["foo"]));
    }

    #[test]
    fn free_var_simple_many() {
        let body = boxparexpr!(ParenExpression::Cons {
            car: Box::new(Expression::Identifier("foo".to_string())),
            cdr: Box::new(Expression::Identifier("bar".to_string()))
        });
        let free_vars = lambda_free_vars("", &body);
        assert_eq!(free_vars, HashSet::from(["foo", "bar"]));
    }

    #[test]
    fn free_var_not_arg() {
        let body = Box::new(Expression::Identifier("foo".to_string()));
        let free_vars = lambda_free_vars("foo", &body);
        assert!(free_vars.is_empty());
    }

    #[test]
    fn free_var_not_arg_but_others() {
        let body = boxparexpr!(ParenExpression::Cons {
            car: Box::new(Expression::Identifier("foo".to_string())),
            cdr: Box::new(Expression::Identifier("bar".to_string()))
        });
        let free_vars = lambda_free_vars("foo", &body);
        assert_eq!(free_vars, HashSet::from(["bar"]));
    }

    #[test]
    fn free_var_not_inner() {
        let body = boxparexpr!(ParenExpression::Binding {
            name: "inner".to_string(),
            value: Box::new(Expression::Number(42)),
            body: Box::new(Expression::Identifier("inner".to_string()))
        });
        let free_vars = lambda_free_vars("", &body);
        assert!(free_vars.is_empty());
    }

    #[test]
    fn free_var_when_shadowed_by_inner() {
        let body = boxparexpr!(ParenExpression::Cons {
            car: Box::new(Expression::Identifier("free".to_string())),
            cdr: boxparexpr!(ParenExpression::Binding {
                name: "free".to_string(),
                value: Box::new(Expression::Number(42)),
                body: Box::new(Expression::Identifier("free".to_string()))
            })
        });
        let free_vars = lambda_free_vars("", &body);
        assert_eq!(free_vars, HashSet::from(["free"]));
    }
}
