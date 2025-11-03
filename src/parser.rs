use std::{collections::HashMap, fmt::Debug};

use crate::tokeniser::Token;
use anyhow::{Result, bail};
use lazy_static::lazy_static;

/// A boxed Expression to allow recursive type structure.
pub type BoxExpr = Box<Expression>;
/// A boxed ParenExpression to allow recursive type structure.
pub type BoxParenExpr = Box<ParenExpression>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expression {
    Number(usize),
    Identifier(String),
    Paren(BoxParenExpr),
    Null,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParenExpression {
    Plus {
        first: BoxExpr,
        second: BoxExpr,
    },
    Minus {
        first: BoxExpr,
        second: BoxExpr,
    },
    Times {
        first: BoxExpr,
        second: BoxExpr,
    },
    Equals {
        first: BoxExpr,
        second: BoxExpr,
    },
    Condition {
        predicate: BoxExpr,
        yes: BoxExpr,
        no: BoxExpr,
    },
    Lambda {
        name: String,
        body: BoxExpr,
    },
    Binding {
        name: String,
        value: BoxExpr,
        body: BoxExpr,
    },
    Cons {
        car: BoxExpr,
        cdr: BoxExpr,
    },
    Car {
        cons: BoxExpr,
    },
    Cdr {
        cons: BoxExpr,
    },
    NullCheck {
        value: BoxExpr,
    },
    Exprs {
        exprs: Vec<BoxExpr>,
    },
}

/// Terminal stack symbols - just the tags from the Token tagged union.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum Terminal {
    LeftParen,
    RightParen,
    Number,
    Identifier,
    Plus,
    Minus,
    Times,
    Equals,
    Condition,
    Lambda,
    Binding,
    Cons,
    Car,
    Cdr,
    NullCheck,
    Null,
}

impl From<Token> for Terminal {
    fn from(value: Token) -> Self {
        match value {
            Token::LeftParen => Self::LeftParen,
            Token::RightParen => Self::RightParen,
            Token::Number(_) => Self::Number,
            Token::Identifier(_) => Self::Identifier,
            Token::Plus => Self::Plus,
            Token::Minus => Self::Minus,
            Token::Times => Self::Times,
            Token::Equals => Self::Equals,
            Token::Condition => Self::Condition,
            Token::Lambda => Self::Lambda,
            Token::Binding => Self::Binding,
            Token::Cons => Self::Cons,
            Token::Car => Self::Car,
            Token::Cdr => Self::Cdr,
            Token::NullCheck => Self::NullCheck,
            Token::Null => Self::Null,
        }
    }
}

/// Non-terminal stack symbols.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum NonTerminal {
    Expression,
    Expressions,
    ParenExpression,
    Epsilon,
    End,
}

/// Parser stack symbols.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum StackSymbol {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

/// Convenience macro for creating a terminal stack symbol by name.
macro_rules! term {
    ($terminal:ident) => {
        StackSymbol::Terminal(Terminal::$terminal)
    };
}

/// Convenience macro for creating a non-terminal stack symbol by name.
macro_rules! nonterm {
    ($nonterminal:ident) => {
        StackSymbol::NonTerminal(NonTerminal::$nonterminal)
    };
}

lazy_static! {
    /// The LL(1) transition table.
    static ref TRANSITION_TABLE: HashMap<(Terminal, NonTerminal), Vec<StackSymbol>> =
        HashMap::from([
            // expression -> number
            (
                (Terminal::Number, NonTerminal::Expression),
                vec![term!(Number)]
            ),
            // expression -> identifier
            (
                (Terminal::Identifier, NonTerminal::Expression),
                vec![term!(Identifier)]
            ),
            // expression -> null
            (
                (Terminal::Null, NonTerminal::Expression),
                vec![term!(Null)]
            ),
            // expression -> paren expression
            (
                (Terminal::LeftParen, NonTerminal::Expression),
                vec![
                    term!(LeftParen),
                    nonterm!(ParenExpression),
                    term!(RightParen)
                ],
            ),
            // expressions -> number
            (
                (Terminal::Number, NonTerminal::Expressions),
                vec![term!(Number), nonterm!(Expressions)]
            ),
            // expressions -> identifier
            (
                (Terminal::Identifier, NonTerminal::Expressions),
                vec![term!(Identifier), nonterm!(Expressions)]
            ),
            // expressions -> null
            (
                (Terminal::Null, NonTerminal::Expressions),
                vec![term!(Null), nonterm!(Expressions)]
            ),
            // expressions -> paren expression
            (
                (Terminal::LeftParen, NonTerminal::Expressions),
                vec![
                    term!(LeftParen),
                    nonterm!(ParenExpression),
                    term!(RightParen),
                    nonterm!(Expressions)
                ],
            ),
            // paren expression -> plus
            (
                (Terminal::Plus, NonTerminal::ParenExpression),
                vec![
                    term!(Plus), nonterm!(Expression), nonterm!(Expression)
                ],
            ),
            // paren expression -> minus
            (
                (Terminal::Minus, NonTerminal::ParenExpression),
                vec![
                    term!(Minus), nonterm!(Expression), nonterm!(Expression)
                ],
            ),
            // paren expression -> times
            (
                (Terminal::Times, NonTerminal::ParenExpression),
                vec![
                    term!(Times), nonterm!(Expression), nonterm!(Expression)
                ],
            ),
            // paren expression -> equals
            (
                (Terminal::Equals, NonTerminal::ParenExpression),
                vec![
                    term!(Equals), nonterm!(Expression), nonterm!(Expression)
                ],
            ),
            // paren expression -> condition
            (
                (Terminal::Condition, NonTerminal::ParenExpression),
                vec![
                    term!(Condition), nonterm!(Expression), nonterm!(Expression), nonterm!(Expression)
                ],
            ),
            // paren expression -> lambda
            (
                (Terminal::Lambda, NonTerminal::ParenExpression),
                vec![
                    term!(Lambda), term!(Identifier), nonterm!(Expression)
                ],
            ),
            // paren expression -> binding
            (
                (Terminal::Binding, NonTerminal::ParenExpression),
                vec![
                    term!(Binding), term!(Identifier), nonterm!(Expression), nonterm!(Expression)
                ],
            ),
            // paren expression -> cons
            (
                (Terminal::Cons, NonTerminal::ParenExpression),
                vec![
                    term!(Cons), nonterm!(Expression), nonterm!(Expression)
                ],
            ),
            // paren expression -> car
            (
                (Terminal::Car, NonTerminal::ParenExpression),
                vec![
                    term!(Car), nonterm!(Expression)
                ],
            ),
            // paren expression -> cdr
            (
                (Terminal::Cdr, NonTerminal::ParenExpression),
                vec![
                    term!(Cdr), nonterm!(Expression)
                ],
            ),
            // paren expression -> nullcheck
            (
                (Terminal::NullCheck, NonTerminal::ParenExpression),
                vec![
                    term!(NullCheck), nonterm!(Expression)
                ],
            ),
            // paren expression -> exprs
            (
                (Terminal::Number, NonTerminal::ParenExpression),
                vec![
                    nonterm!(Expressions)
                ],
            ),
            // paren expression -> exprs
            (
                (Terminal::Identifier, NonTerminal::ParenExpression),
                vec![
                    nonterm!(Expressions)
                ],
            ),
            // paren expression -> exprs
            (
                (Terminal::LeftParen, NonTerminal::ParenExpression),
                vec![
                    nonterm!(Expressions)
                ],
            ),
            // exprs -> right paren
            (
                (Terminal::RightParen, NonTerminal::Expressions),
                vec![nonterm!(Epsilon)],
            ),
        ]);
}

/// A builder for Expressions.
#[derive(Debug)]
pub struct ExprBuilder {
    value: Option<BoxExpr>,
}

impl ExprBuilder {
    fn new() -> Self {
        Self { value: None }
    }

    fn take(&mut self, expr: BoxExpr) -> Result<()> {
        if self.value.is_some() {
            bail!("Something went wrong internally; can't add terms to a finished expression.")
        }

        self.value = Some(expr);
        Ok(())
    }

    fn finish(&mut self) -> Result<BoxExpr> {
        if self.value.is_none() {
            bail!("Something went wrong internally; can't finish an expression with no value.")
        }

        Ok(self.value.clone().unwrap())
    }

    fn finished(&self) -> bool {
        self.value.is_some()
    }
}

/// A builder for ParenExpressions.
#[derive(Debug)]
pub struct ParenExprBuilder {
    token: Token,
    terms: Vec<BoxExpr>,
    terms_finished: bool,
    paren_closed: bool,
}

/// Convenience macro for creating a BoxExpr from a ParenExpression.
macro_rules! boxparexpr {
    ($parexpr:expr) => {
        Box::new(Expression::Paren(Box::new($parexpr)))
    };
}

impl ParenExprBuilder {
    fn new(token: Token) -> Result<Self> {
        match token {
            Token::RightParen => {
                bail!("First token in a paren expression can't be a ')'.")
            }
            _ => Ok(Self {
                token,
                terms: Vec::new(),
                terms_finished: false,
                paren_closed: false,
            }),
        }
    }

    fn take(&mut self, expr: BoxExpr) -> Result<()> {
        if self.finished() {
            bail!(
                "Something went wrong internally; can't add terms to a finished paren expression."
            )
        }

        match &self.token {
            Token::LeftParen | Token::Number(_) | Token::Identifier(_) | Token::Null => {
                self.terms.push(expr);
                self.terms_finished = true;
            }
            Token::Plus => {
                self.terms.push(expr);
                if self.terms.len() == 2 {
                    self.terms_finished = true;
                }
            }
            Token::Minus => {
                self.terms.push(expr);
                if self.terms.len() == 2 {
                    self.terms_finished = true;
                }
            }
            Token::Times => {
                self.terms.push(expr);
                if self.terms.len() == 2 {
                    self.terms_finished = true;
                }
            }
            Token::Equals => {
                self.terms.push(expr);
                if self.terms.len() == 2 {
                    self.terms_finished = true;
                }
            }
            Token::Condition => {
                self.terms.push(expr);
                if self.terms.len() == 3 {
                    self.terms_finished = true;
                }
            }
            Token::Lambda => {
                if self.terms.is_empty() {
                    if let Expression::Identifier(_) = &*expr {
                        self.terms.push(expr);
                    } else {
                        bail!("The first term of a lambda must be an identifier, not {expr:?}")
                    }
                } else {
                    self.terms.push(expr);
                    if self.terms.len() == 2 {
                        self.terms_finished = true;
                    }
                }
            }
            Token::Binding => {
                if self.terms.is_empty() {
                    if let Expression::Identifier(_) = &*expr {
                        self.terms.push(expr);
                    } else {
                        bail!("The first term of a binding must be an identifier, not {expr:?}")
                    }
                } else {
                    self.terms.push(expr);
                    if self.terms.len() == 3 {
                        self.terms_finished = true;
                    }
                }
            }
            Token::Cons => {
                self.terms.push(expr);
                if self.terms.len() == 2 {
                    self.terms_finished = true;
                }
            }
            Token::Car => {
                self.terms.push(expr);
                if self.terms.len() == 1 {
                    self.terms_finished = true;
                }
            }
            Token::Cdr => {
                self.terms.push(expr);
                if self.terms.len() == 1 {
                    self.terms_finished = true;
                }
            }
            Token::NullCheck => {
                self.terms.push(expr);
                if self.terms.len() == 1 {
                    self.terms_finished = true;
                }
            }
            other => bail!(
                "Something went wrong internally; can't build a paren expression for the token {other:?}",
            ),
        }

        Ok(())
    }

    fn finish(&mut self) -> Result<BoxExpr> {
        if !self.finished() {
            bail!("Something went wrong internally; can't finish an unfinished paren expression.")
        }

        match &self.token {
            Token::LeftParen => Ok(boxparexpr!(ParenExpression::Exprs {
                exprs: self.terms.clone()
            })),
            Token::Number(num) => {
                let mut exprs = vec![Box::new(Expression::Number(*num))];
                exprs.extend(self.terms.clone());
                Ok(boxparexpr!(ParenExpression::Exprs { exprs }))
            }
            Token::Identifier(ident) => {
                let mut exprs = vec![Box::new(Expression::Identifier(ident.clone()))];
                exprs.extend(self.terms.clone());
                Ok(boxparexpr!(ParenExpression::Exprs { exprs }))
            }
            Token::Null => {
                let mut exprs = vec![Box::new(Expression::Null)];
                exprs.extend(self.terms.clone());
                Ok(boxparexpr!(ParenExpression::Exprs { exprs }))
            }
            Token::Plus => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a plus expression takes 2 terms, not {}.",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Plus { first, second }))
            }
            Token::Minus => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a minus expression takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Minus { first, second }))
            }
            Token::Times => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a times expression takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Times { first, second }))
            }
            Token::Equals => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because an equals expression takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Equals { first, second }))
            }
            Token::Condition => {
                if self.terms.len() != 3 {
                    bail!(
                        "Program must be invalid, because a conditional takes 3 terms, not {}",
                        self.terms.len()
                    )
                }
                let no = self.terms.pop().unwrap();
                let yes = self.terms.pop().unwrap();
                let predicate = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Condition {
                    predicate,
                    yes,
                    no
                }))
            }
            Token::Lambda => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a lambda takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let body = self.terms.pop().unwrap();
                let name_expr = self.terms.pop().unwrap();

                if let Expression::Identifier(name) = *name_expr {
                    Ok(boxparexpr!(ParenExpression::Lambda { name, body }))
                } else {
                    bail!(
                        "Program must be invalid, because a lambdas first term must be an identifier."
                    )
                }
            }
            Token::Binding => {
                if self.terms.len() != 3 {
                    bail!(
                        "Program must be invalid, because a binding takes 3 terms, not {}",
                        self.terms.len()
                    )
                }
                let body = self.terms.pop().unwrap();
                let value = self.terms.pop().unwrap();
                let name_expr = self.terms.pop().unwrap();

                if let Expression::Identifier(name) = *name_expr {
                    Ok(boxparexpr!(ParenExpression::Binding { name, value, body }))
                } else {
                    bail!(
                        "Program must be invalid, because a bindings first term must be an identifier."
                    )
                }
            }
            Token::Cons => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a cons expression takes 2 terms, not {}.",
                        self.terms.len()
                    )
                }
                let car = self.terms.pop().unwrap();
                let cdr = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Cons { car, cdr }))
            }
            Token::Car => {
                if self.terms.len() != 1 {
                    bail!(
                        "Program must be invalid, because a car expression takes 1 term, not {}.",
                        self.terms.len()
                    )
                }
                let cons = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Car { cons }))
            }
            Token::Cdr => {
                if self.terms.len() != 1 {
                    bail!(
                        "Program must be invalid, because a cdr expression takes 1 term, not {}.",
                        self.terms.len()
                    )
                }
                let cons = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Cdr { cons }))
            }
            Token::NullCheck => {
                if self.terms.len() != 1 {
                    bail!(
                        "Program must be invalid, because a null check expression takes 1 term, not {}.",
                        self.terms.len()
                    )
                }
                let value = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::NullCheck { value }))
            }
            other => bail!(
                "Something went wrong internally; can't finish a paren expression for the token {other:?}",
            ),
        }
    }

    fn close_paren(&mut self) {
        self.paren_closed = true;
    }

    fn finished(&self) -> bool {
        self.terms_finished && self.paren_closed
    }
}

#[derive(Debug)]
enum Builder {
    Expr(ExprBuilder),
    Paren(ParenExprBuilder),
}

/// Generic interface for building an expression or paren expression.
impl Builder {
    /// Add an expression to the expression we are building.
    fn take(&mut self, expr: BoxExpr) -> Result<()> {
        match self {
            Self::Expr(expr_builder) => expr_builder.take(expr),
            Self::Paren(parexpr_builder) => parexpr_builder.take(expr),
        }
    }

    /// Consume the builder and return the finished expression.
    fn finish(&mut self) -> Result<BoxExpr> {
        match self {
            Self::Expr(expr_builder) => expr_builder.finish(),
            Self::Paren(parexpr_builder) => parexpr_builder.finish(),
        }
    }

    /// Is the builder ready to be consumed?
    fn finished(&self) -> bool {
        match self {
            Self::Expr(expr_builder) => expr_builder.finished(),
            Self::Paren(parexpr_builder) => parexpr_builder.finished(),
        }
    }
}

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
                    if let Token::Identifier(ident) = token {
                        top_expr.take(Box::new(Expression::Identifier(ident)))?;
                    } else if let Token::Number(num) = token {
                        top_expr.take(Box::new(Expression::Number(num)))?;
                    } else if Token::Null == token {
                        top_expr.take(Box::new(Expression::Null))?;
                    } else if let Builder::Paren(ref mut parexpr_builder) = top_expr
                        && Token::RightParen == token
                    {
                        parexpr_builder.close_paren();
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
                } else {
                    bail!(
                        "The program must be invalid, because a
    {token:?} was seen when a
    {term_symb:?} was expected."
                    )
                }
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
                        NonTerminal::Expressions => {
                            builder_stack.push(Builder::Expr(ExprBuilder::new()));
                        }
                        NonTerminal::ParenExpression => {
                            builder_stack
                                .push(Builder::Paren(ParenExprBuilder::new(token.clone())?));
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
                "Something went wrong internally; the program was recognised, but the AST wasn't finished.
    The expression builder stack looks like:
    {builder_stack:?}"
            )
        }
    } else {
        bail!(
            "The program must be invalid, because the input token stack was
    {tokens:?}
and the symbol stack was
    {symbols:?}"
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::tokeniser::tokenise;

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
    fn parse_lambda() {
        assert_eq!(
            parse(tokenise("((λ x (+ x 1)) 5)").unwrap()).unwrap(),
            boxparexpr!(ParenExpression::Exprs {
                exprs: vec![
                    boxparexpr!(ParenExpression::Lambda {
                        name: "x".to_string(),
                        body: boxparexpr!(ParenExpression::Plus {
                            first: Box::new(Expression::Identifier("x".to_string())),
                            second: Box::new(Expression::Number(1))
                        })
                    }),
                    Box::new(Expression::Number(5))
                ]
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
            parse(tokenise("(≜ x 10 (+ x x)) ").unwrap()).unwrap(),
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
}
