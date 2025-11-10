use anyhow::{Result, bail};

use crate::{
    ast::{BoxExpr, Builder, ExprBuilder, ParenExprBuilder, PattClauseBuilder},
    tokeniser::Token,
};

#[macro_use]
mod symbols;

pub use symbols::*;

/// Parse a list of tokens and return an AST - a single expression.
pub fn parse(mut tokens: Vec<Token>) -> Result<BoxExpr> {
    tokens.reverse();
    let mut builder_stack: Vec<Builder> = vec![Builder::Expr(ExprBuilder::new())];
    let mut root_expr: Option<BoxExpr> = None;
    let mut symbols = vec![nonterm!(End), nonterm!(Expression)];

    while !tokens.is_empty() && !symbols.is_empty() {
        let token = tokens.pop().unwrap();
        let symbol = symbols.pop().unwrap();

        match &symbol {
            StackSymbol::Terminal(term_symb) => {
                if *term_symb == token.clone().into() {
                    // --- Building AST ---
                    if builder_stack.is_empty() {
                        bail!(
                            "Something went wrong internally; the expression builder stack is empty."
                        )
                    }
                    let mut top_expr = builder_stack.pop().unwrap();
                    if let Ok(token_expr) = token.clone().try_into() {
                        top_expr.take(token_expr)?;
                    } else if let Builder::Paren(ref mut parexpr_builder) = top_expr
                        && Token::RightParen == token
                    {
                        parexpr_builder.close_paren();
                    } else if let Builder::PatternClause(ref mut pattclause_builder) = top_expr
                        && Token::RightParen == token
                    {
                        pattclause_builder.close_paren();
                    }

                    while top_expr.finished() {
                        let finished_expr = top_expr.finish()?;
                        if builder_stack.is_empty() {
                            root_expr = Some(finished_expr);
                            break;
                        }
                        top_expr = builder_stack.pop().unwrap();
                        top_expr.take(finished_expr)?;
                    }

                    builder_stack.push(top_expr);
                    // --------------------
                    continue;
                }
                bail!(
                    "The program must be invalid, because a
                {token:?} was seen when a
                {term_symb:?} was expected."
                )
            }

            StackSymbol::NonTerminal(nonterm_symb) => {
                if let Some(new_symbols) =
                    TRANSITION_TABLE.get(&(token.clone().into(), nonterm_symb.clone()))
                {
                    // --- Building AST ---
                    match nonterm_symb {
                        NonTerminal::Expression => {
                            builder_stack.push(Builder::Expr(ExprBuilder::new()));
                        }
                        NonTerminal::ParenExpression => {
                            builder_stack
                                .push(Builder::Paren(ParenExprBuilder::new(token.clone())?));
                        }
                        NonTerminal::PatternClauses => {
                            builder_stack.push(Builder::PatternClause(PattClauseBuilder::new()));
                        }
                        NonTerminal::End => bail!(
                            "Something went wrong internally; found transition for the end symbol!"
                        ),
                        NonTerminal::Epsilon => bail!(
                            "Something went wrong internally; found transition for the epsilon symbol!"
                        ),
                    }
                    // --------------------

                    symbols.extend(new_symbols.iter().cloned().rev());
                    tokens.push(token);
                } else if *nonterm_symb == NonTerminal::Epsilon {
                    builder_stack.pop();
                    tokens.push(token);
                } else {
                    bail!(
                        "The program must be invalid, because
    {symbol:?} was on the symbol stack and
    {token:?} was the next input token."
                    )
                }
            }
        }
    }

    if tokens.is_empty() && symbols.len() == 1 && symbols.pop().unwrap() == nonterm!(End) {
        if let Some(expr) = root_expr {
            Ok(expr)
        } else {
            bail!(
                "Something went wrong internally; the program was recognised, \
                 but the AST wasn't finished. The expression builder stack looks like:
    {builder_stack:#?}"
            )
        }
    } else {
        bail!(
            "The program must be invalid, because the input token stack was
    {tokens:#?}
and the symbol stack was
    {symbols:#?}"
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{Expression, ParenExpression, Pattern, PatternClause},
        tokeniser::tokenise,
    };

    use super::*;

    #[test]
    fn parse_number() {
        assert_eq!(
            parse(tokenise("42").unwrap()).unwrap(),
            Box::new(Expression::Number(42))
        );
    }

    #[test]
    fn parse_addition() {
        assert_eq!(
            parse(tokenise("(+ 123 456)").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Plus {
                first: Box::new(Expression::Number(123)),
                second: Box::new(Expression::Number(456))
            })
        );
    }

    #[test]
    fn parse_arithmetic() {
        assert_eq!(
            parse(tokenise("(+ (× 1 42) (− 42 0))").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Plus {
                first: boxparexpr!(ParenExpression::Times {
                    first: Box::new(Expression::Number(1)),
                    second: Box::new(Expression::Number(42))
                }),
                second: boxparexpr!(ParenExpression::Minus {
                    first: Box::new(Expression::Number(42)),
                    second: Box::new(Expression::Number(0))
                })
            })
        );
    }

    #[test]
    fn parse_conditional() {
        assert_eq!(
            parse(tokenise("(? (= 1 1) 10 20)").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Condition {
                predicate: boxparexpr!(ParenExpression::Equals {
                    first: Box::new(Expression::Number(1)),
                    second: Box::new(Expression::Number(1))
                }),
                yes: Box::new(Expression::Number(10)),
                no: Box::new(Expression::Number(20))
            })
        );
    }

    #[test]
    fn parse_lambda_immediate() {
        assert_eq!(
            parse(tokenise("((λ x (+ x 1)) 5)").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Application {
                lambda: boxparexpr!(ParenExpression::Lambda {
                    arg: "x".to_string(),
                    body: boxparexpr!(ParenExpression::Plus {
                        first: Box::new(Expression::Identifier("x".to_string())),
                        second: Box::new(Expression::Number(1))
                    })
                }),
                argument: Box::new(Expression::Number(5))
            })
        )
    }

    #[test]
    fn parse_lambda_bound() {
        assert_eq!(
            parse(tokenise("(≜ add-one (λ x (+ x 1)) (add-one 5))").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Binding {
                name: "add-one".to_string(),
                value: boxparexpr!(ParenExpression::Lambda {
                    arg: "x".to_string(),
                    body: boxparexpr!(ParenExpression::Plus {
                        first: Box::new(Expression::Identifier("x".to_string())),
                        second: Box::new(Expression::Number(1))
                    })
                }),
                body: boxparexpr!(ParenExpression::Application {
                    lambda: Box::new(Expression::Identifier("add-one".to_string())),
                    argument: Box::new(Expression::Number(5))
                })
            })
        )
    }

    #[test]
    fn dont_parse_lambda_extra_terms() {
        assert!(parse(tokenise("((λ x (+ x 1) 42) 5)").unwrap()).is_err());
    }

    #[test]
    fn parse_binding() {
        assert_eq!(
            parse(tokenise("(≜ x 10 (+ x x))").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Binding {
                name: "x".to_string(),
                value: Box::new(Expression::Number(10)),
                body: boxparexpr!(ParenExpression::Plus {
                    first: Box::new(Expression::Identifier("x".to_string())),
                    second: Box::new(Expression::Identifier("x".to_string()))
                })
            })
        );
    }

    #[test]
    fn parse_comparison() {
        assert_eq!(
            parse(tokenise("(≜ x 10 (‹ x (+ x 1)))").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Binding {
                name: "x".to_string(),
                value: Box::new(Expression::Number(10)),
                body: boxparexpr!(ParenExpression::LessThan {
                    first: Box::new(Expression::Identifier("x".to_string())),
                    second: boxparexpr!(ParenExpression::Plus {
                        first: Box::new(Expression::Identifier("x".to_string())),
                        second: Box::new(Expression::Number(1))
                    })
                })
            })
        );
    }

    #[test]
    fn parse_logic() {
        assert_eq!(
            parse(tokenise("(∧ 1 (∨ 0 (¬ 0)))").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::LogicalAnd {
                first: Box::new(Expression::Number(1)),
                second: boxparexpr!(ParenExpression::LogicalOr {
                    first: Box::new(Expression::Number(0)),
                    second: boxparexpr!(ParenExpression::LogicalNot {
                        value: Box::new(Expression::Number(0))
                    })
                })
            })
        );
    }

    #[test]
    fn parse_lists() {
        assert_eq!(
            parse(tokenise("(≜ lst (∷ 42 (∷ 99 ∅)) (∨ (∘ (← lst)) (∘ (→ (→ lst)))))").unwrap())
                .unwrap(),
            boxparexpr!(ParenExpression::Binding {
                name: "lst".to_string(),
                value: boxparexpr!(ParenExpression::Cons {
                    car: Box::new(Expression::Number(42)),
                    cdr: boxparexpr!(ParenExpression::Cons {
                        car: Box::new(Expression::Number(99)),
                        cdr: Box::new(Expression::Null)
                    })
                }),
                body: boxparexpr!(ParenExpression::LogicalOr {
                    first: boxparexpr!(ParenExpression::NullCheck {
                        value: boxparexpr!(ParenExpression::Car {
                            cons: Box::new(Expression::Identifier("lst".to_string()))
                        })
                    }),
                    second: boxparexpr!(ParenExpression::NullCheck {
                        value: boxparexpr!(ParenExpression::Cdr {
                            cons: boxparexpr!(ParenExpression::Cdr {
                                cons: Box::new(Expression::Identifier("lst".to_string()))
                            })
                        })
                    })
                })
            })
        );
    }

    #[test]
    fn parse_match() {
        assert_eq!(
            parse(
                tokenise(
                    "(⊢ 42
                        (42 1)
                        (99 0))",
                )
                .unwrap(),
            )
            .unwrap(),
            boxparexpr!(ParenExpression::Match {
                value: Box::new(Expression::Number(42)),
                patterns: vec![
                    Box::new(PatternClause {
                        pattern: Box::new(Pattern::Number(42)),
                        body: Box::new(Expression::Number(1))
                    }),
                    Box::new(PatternClause {
                        pattern: Box::new(Pattern::Number(99)),
                        body: Box::new(Expression::Number(0))
                    })
                ]
            })
        );
    }

    #[test]
    fn parse_match_cons() {
        assert_eq!(
            parse(
                tokenise(
                    "(⊢ (∷ 42 99)
                        (∅ 0)
                        ((∷ x _) x))",
                )
                .unwrap(),
            )
            .unwrap(),
            boxparexpr!(ParenExpression::Match {
                value: boxparexpr!(ParenExpression::Cons {
                    car: Box::new(Expression::Number(42)),
                    cdr: Box::new(Expression::Number(99))
                }),
                patterns: vec![
                    Box::new(PatternClause {
                        pattern: Box::new(Pattern::Null),
                        body: Box::new(Expression::Number(0))
                    }),
                    Box::new(PatternClause {
                        pattern: Box::new(Pattern::Cons((
                            Box::new(Pattern::Identifier("x".to_string())),
                            Box::new(Pattern::Wildcard)
                        ))),
                        body: Box::new(Expression::Identifier("x".to_string()))
                    })
                ]
            })
        );
    }

    #[test]
    fn parse_unbound_ident() {
        assert!(parse(tokenise("(⌒)").unwrap()).is_err());
    }
}
