use crate::tokeniser::Token;
use anyhow::{Error, Result, bail};

// AST NODES

/// A boxed Expression to allow recursive type structure.
pub type BoxExpr = Box<Expression>;
/// A boxed ParenExpression to allow recursive type structure.
pub type BoxParenExpr = Box<ParenExpression>;
/// A boxed PatternClause to allow recursive type structure.
pub type BoxPattClause = Box<PatternClause>;
/// A boxed Pattern to allow recursive type structure.
pub type BoxPatt = Box<Pattern>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expression {
    Number(usize),
    Identifier(String),
    Paren(BoxParenExpr),
    Null,
    Wildcard,
    PatternClause(BoxPattClause),
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
    LessThan {
        first: BoxExpr,
        second: BoxExpr,
    },
    GreaterThan {
        first: BoxExpr,
        second: BoxExpr,
    },
    LogicalAnd {
        first: BoxExpr,
        second: BoxExpr,
    },
    LogicalOr {
        first: BoxExpr,
        second: BoxExpr,
    },
    LogicalNot {
        value: BoxExpr,
    },
    Match {
        value: BoxExpr,
        patterns: Vec<BoxPattClause>,
    },
    Exprs {
        exprs: Vec<BoxExpr>,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PatternClause {
    pattern: BoxPatt,
    body: BoxExpr,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Number(usize),
    Identifier(String),
    Null,
    Wildcard,
    Cons((BoxPatt, BoxPatt)),
}

impl TryFrom<BoxExpr> for BoxPatt {
    type Error = Error;

    fn try_from(value: BoxExpr) -> std::result::Result<Self, Self::Error> {
        Ok(Box::new(match *value {
            Expression::Number(num) => Pattern::Number(num),
            Expression::Identifier(ident) => Pattern::Identifier(ident),
            Expression::Null => Pattern::Null,
            Expression::Wildcard => Pattern::Wildcard,
            Expression::Paren(parexpr) => {
                if let ParenExpression::Cons { car, cdr } = *parexpr {
                    Pattern::Cons((car.try_into()?, cdr.try_into()?))
                } else {
                    bail!(
                        "The program must be invalid, because {parexpr:?} is not a valid pattern."
                    )
                }
            }
            Expression::PatternClause(patt_clause) => bail!(
                "The program must be invalid, because it looks like there is an entire pattern clause \
                (the tuple `(pattern, expression)`) where just a pattern was expected. Check your brackets. \
                The clause found was:
    {patt_clause:?}"
            ),
        }))
    }
}

// NODE BUILDERS

/// A builder for Expressions.
#[derive(Debug)]
pub struct ExprBuilder {
    value: Option<BoxExpr>,
}

impl ExprBuilder {
    pub fn new() -> Self {
        Self { value: None }
    }

    pub fn take(&mut self, expr: BoxExpr) -> Result<()> {
        if self.value.is_some() {
            bail!("Something went wrong internally; can't add terms to a finished expression.")
        }

        self.value = Some(expr);
        Ok(())
    }

    pub fn finish(&mut self) -> Result<BoxExpr> {
        if self.value.is_none() {
            bail!("Something went wrong internally; can't finish an expression with no value.")
        }

        Ok(self.value.clone().unwrap())
    }

    pub fn finished(&self) -> bool {
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

/// Convenience macro for creating a `BoxExpr` from a `ParenExpression`.
macro_rules! boxparexpr {
    ($parexpr:expr) => {
        Box::new(Expression::Paren(Box::new($parexpr)))
    };
}

impl ParenExprBuilder {
    pub fn new(token: Token) -> Result<Self> {
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

    pub fn take(&mut self, expr: BoxExpr) -> Result<()> {
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
            Token::Match => {
                if self.terms.is_empty() {
                    self.terms.push(expr);
                } else if let Expression::PatternClause(_) = *expr {
                    self.terms.push(expr);
                    self.terms_finished = true;
                } else {
                    bail!(
                        "The program must be invalid, because a match statement can only contain \
                           a value to match and a sequence of pattern clauses, not:
    {expr:?}"
                    )
                }
            }
            Token::Plus
            | Token::Minus
            | Token::Times
            | Token::Equals
            | Token::Cons
            | Token::LessThan
            | Token::GreaterThan
            | Token::LogicalAnd
            | Token::LogicalOr => {
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
            Token::Car | Token::Cdr | Token::NullCheck | Token::LogicalNot => {
                self.terms.push(expr);
                if self.terms.len() == 1 {
                    self.terms_finished = true;
                }
            }
            Token::RightParen => bail!(
                "Something went wrong internally; can't build a paren expression \
                 that started with a right parenthesis.",
            ),
            Token::Wildcard => bail!(
                "Something went wrong internally; can't build a paren expression \
                 that started with a wildcard.",
            ),
        }

        Ok(())
    }

    #[allow(clippy::similar_names, clippy::too_many_lines)]
    pub fn finish(&mut self) -> Result<BoxExpr> {
        if !self.finished() {
            bail!("Something went wrong internally; can't finish an unfinished paren expression.")
        }

        match &self.token {
            Token::LeftParen => Ok(boxparexpr!(ParenExpression::Exprs {
                exprs: self.terms.clone()
            })),
            Token::Match => {
                if self.terms.len() < 2 {
                    bail!(
                        "Something went wrong internally; can't finish a match expression \
                         with less than two terms."
                    )
                }
                let mut term_iter = self.terms.iter();
                let value = term_iter.next().unwrap().to_owned();
                let mut patterns = Vec::new();
                for expr in term_iter {
                    if let Expression::PatternClause(ref clause) = **expr {
                        patterns.push(clause.to_owned());
                    } else {
                        bail!(
                            "Something went wrong internally; can't use a {expr:?} as a pattern clause."
                        )
                    }
                }
                Ok(boxparexpr!(ParenExpression::Match { value, patterns }))
            }

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
                        "Program must be invalid, because a plus expression \
                         takes 2 terms, not {}.",
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
                        "Program must be invalid, because a minus expression \
                         takes 2 terms, not {}",
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
                        "Program must be invalid, because a times expression \
                         takes 2 terms, not {}",
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
                        "Program must be invalid, because an equals expression \
                         takes 2 terms, not {}",
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
                        "Program must be invalid, because a conditional \
                         takes 3 terms, not {}",
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
                        "Program must be invalid, because a lambdas first term \
                         must be an identifier."
                    )
                }
            }
            Token::Binding => {
                if self.terms.len() != 3 {
                    bail!(
                        "Program must be invalid, because a binding takes \
                         3 terms, not {}",
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
                        "Program must be invalid, because a bindings first term \
                         must be an identifier."
                    )
                }
            }
            Token::Cons => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a cons expression \
                         takes 2 terms, not {}.",
                        self.terms.len()
                    )
                }
                let cdr = self.terms.pop().unwrap();
                let car = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Cons { car, cdr }))
            }
            Token::Car => {
                if self.terms.len() != 1 {
                    bail!(
                        "Program must be invalid, because a car expression \
                         takes 1 term, not {}.",
                        self.terms.len()
                    )
                }
                let cons = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Car { cons }))
            }
            Token::Cdr => {
                if self.terms.len() != 1 {
                    bail!(
                        "Program must be invalid, because a cdr expression \
                         takes 1 term, not {}.",
                        self.terms.len()
                    )
                }
                let cons = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Cdr { cons }))
            }
            Token::NullCheck => {
                if self.terms.len() != 1 {
                    bail!(
                        "Program must be invalid, because a null check expression \
                         takes 1 term, not {}.",
                        self.terms.len()
                    )
                }
                let value = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::NullCheck { value }))
            }
            Token::LessThan => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a less than expression \
                         takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::LessThan { first, second }))
            }
            Token::GreaterThan => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a greater than expression \
                         takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::GreaterThan { first, second }))
            }
            Token::LogicalAnd => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a logical \"and\" expression \
                         takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::LogicalAnd { first, second }))
            }
            Token::LogicalOr => {
                if self.terms.len() != 2 {
                    bail!(
                        "Program must be invalid, because a logical \"or\" expression \
                         takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let second = self.terms.pop().unwrap();
                let first = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::LogicalOr { first, second }))
            }
            Token::LogicalNot => {
                if self.terms.len() != 1 {
                    bail!(
                        "Program must be invalid, because a logical \"not\" expression \
                         takes 2 terms, not {}",
                        self.terms.len()
                    )
                }
                let value = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::LogicalNot { value }))
            }
            Token::RightParen | Token::Wildcard => bail!(
                "Something went wrong internally; can't finish a paren expression \
                 that started with a right parenthesis or a wildcard.",
            ),
        }
    }

    pub fn close_paren(&mut self) {
        self.paren_closed = true;
    }

    pub fn finished(&self) -> bool {
        self.terms_finished && self.paren_closed
    }
}

/// A builder for PatternClauses.
#[derive(Debug)]
pub struct PattClauseBuilder {
    pattern: Option<BoxPatt>,
    body: Option<BoxExpr>,
    finished: bool,
}

impl PattClauseBuilder {
    pub fn new() -> Self {
        Self {
            pattern: None,
            body: None,
            finished: false,
        }
    }

    fn take(&mut self, expr: BoxExpr) -> Result<()> {
        if self.pattern.is_none() {
            self.pattern = Some(expr.try_into()?);
        } else if self.body.is_none() {
            self.body = Some(expr);
            self.finished = true;
        } else {
            bail!("Something went wrong internally; can't add terms to a finished pattern clause.")
        }

        Ok(())
    }

    fn finish(&mut self) -> Result<BoxExpr> {
        if !self.finished {
            bail!("Something went wrong internally; can't finish an unfinished pattern clause.")
        }

        Ok(Box::new(Expression::PatternClause(Box::new(
            PatternClause {
                pattern: self.pattern.clone().unwrap(),
                body: self.body.clone().unwrap(),
            },
        ))))
    }

    fn finished(&self) -> bool {
        self.finished
    }
}

#[derive(Debug)]
pub enum Builder {
    Expr(ExprBuilder),
    Paren(ParenExprBuilder),
    PatternClause(PattClauseBuilder),
}

/// Generic interface for building a composite form.
impl Builder {
    /// Add an expression to the expression we are building.
    pub fn take(&mut self, expr: BoxExpr) -> Result<()> {
        match self {
            Self::Expr(expr_builder) => expr_builder.take(expr),
            Self::Paren(parexpr_builder) => parexpr_builder.take(expr),
            Self::PatternClause(pattclause_builder) => pattclause_builder.take(expr),
        }
    }

    /// Consume the builder and return the finished expression.
    pub fn finish(&mut self) -> Result<BoxExpr> {
        match self {
            Self::Expr(expr_builder) => expr_builder.finish(),
            Self::Paren(parexpr_builder) => parexpr_builder.finish(),
            Self::PatternClause(pattclause_builder) => pattclause_builder.finish(),
        }
    }

    /// Is the builder ready to be consumed?
    pub fn finished(&self) -> bool {
        match self {
            Self::Expr(expr_builder) => expr_builder.finished(),
            Self::Paren(parexpr_builder) => parexpr_builder.finished(),
            Self::PatternClause(pattclause_builder) => pattclause_builder.finished(),
        }
    }
}
