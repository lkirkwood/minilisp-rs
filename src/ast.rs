use crate::tokeniser::Token;
use anyhow::{Error, Result, bail};

// AST NODES

/// A boxed Expression to allow recursive type structure.
pub type BoxExpr = Box<Expression>;
/// A boxed `ParenExpression` to allow recursive type structure.
pub type BoxParenExpr = Box<ParenExpression>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expression {
    Number(isize),
    Identifier(String),
    Paren(BoxParenExpr),
    Null,
}

impl TryFrom<Token> for BoxExpr {
    type Error = Error;
    fn try_from(value: Token) -> std::result::Result<Self, Self::Error> {
        match value {
            Token::Number(num) => Ok(Box::new(Expression::Number(num))),
            Token::Identifier(ident) => Ok(Box::new(Expression::Identifier(ident))),
            Token::Null => Ok(Box::new(Expression::Null)),
            Token::LeftParen
            | Token::RightParen
            | Token::Plus
            | Token::Minus
            | Token::Times
            | Token::Equals
            | Token::Condition
            | Token::Lambda
            | Token::Binding
            | Token::Cons
            | Token::Car
            | Token::Cdr
            | Token::NullCheck
            | Token::LessThan
            | Token::GreaterThan
            | Token::LogicalAnd
            | Token::LogicalOr
            | Token::LogicalNot => {
                bail!("Not a token that can be converted to an expression directly: {value:?}")
            }
        }
    }
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
        arg: String,
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
    Application {
        lambda: BoxExpr,
        argument: BoxExpr,
    },
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

    pub fn build(&mut self) -> Result<BoxExpr> {
        if self.value.is_none() {
            bail!("Something went wrong internally; can't finish an expression with no value.")
        }

        Ok(self.value.clone().unwrap())
    }

    pub fn finished(&self) -> bool {
        self.value.is_some()
    }
}

/// A builder for `ParenExpressions`.
#[derive(Debug)]
pub struct ParenExprBuilder {
    token: Token,
    terms: Vec<BoxExpr>,
    terms_finished: bool,
}

/// Convenience macro for creating a `BoxExpr` from a `ParenExpression`.
macro_rules! boxparexpr {
    ($parexpr:expr) => {
        Box::new(Expression::Paren(Box::new($parexpr)))
    };
}

macro_rules! build_two_arg_parexpr {
    ($terms:expr, $op_variant:ident) => {{
        if $terms.len() != 2 {
            bail!(
                "Something went wrong internally; tried to build a {} expression \
                    with {} terms, instead of 2.",
                stringify!($op_variant),
                $terms.len()
            )
        }
        let second = $terms.pop().unwrap();
        let first = $terms.pop().unwrap();
        Ok(boxparexpr!(ParenExpression::$op_variant { first, second }))
    }};
}

impl ParenExprBuilder {
    pub fn new(token: Token) -> Result<Self> {
        match token {
            Token::RightParen | Token::Null | Token::Number(_) => {
                bail!(
                    "Something went wrong internally; first token in a paren expression \
                     can't be a {token:?}."
                )
            }
            _ => Ok(Self {
                token,
                terms: Vec::new(),
                terms_finished: false,
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
            Token::Plus
            | Token::LeftParen
            | Token::Identifier(_)
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
                        bail!(
                            "Something went wrong internally; \
                            the first term of a lambda must be an identifier, not {expr:?}"
                        )
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
                        bail!(
                            "Something went wrong internally; \
                            The first term of a binding must be an identifier, not {expr:?}"
                        )
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
            Token::RightParen | Token::Null | Token::Number(_) => bail!(
                "Something went wrong internally; can't build a paren expression \
                 that started with a {:?}.",
                self.token
            ),
        }

        Ok(())
    }

    #[allow(clippy::similar_names, clippy::too_many_lines)]
    pub fn build(&mut self) -> Result<BoxExpr> {
        if !self.finished() {
            bail!("Something went wrong internally; can't finish an unfinished paren expression.")
        }

        match &self.token {
            Token::LeftParen | Token::Identifier(_) => {
                if self.terms.len() < 2 {
                    bail!(
                        "Something went wrong internally; can't finish a lambda application \
                         expression with less than two terms."
                    )
                }
                dbg!(&self.terms);

                let argument = self.terms.pop().unwrap();
                let lambda = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Application {
                    lambda,
                    argument
                }))
            }
            Token::Plus => {
                build_two_arg_parexpr!(self.terms, Plus)
            }
            Token::Minus => {
                build_two_arg_parexpr!(self.terms, Minus)
            }
            Token::Times => {
                build_two_arg_parexpr!(self.terms, Times)
            }
            Token::Equals => {
                build_two_arg_parexpr!(self.terms, Equals)
            }
            Token::Condition => {
                if self.terms.len() != 3 {
                    bail!(
                        "Something went wrong internally; tried to build a conditional \
                         with {} terms instead of 3.",
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
                        "Something went wrong internally; tried to build a lambda \
                        with {} terms instead of 2.",
                        self.terms.len()
                    )
                }
                let body = self.terms.pop().unwrap();
                let arg_expr = self.terms.pop().unwrap();

                if let Expression::Identifier(arg) = *arg_expr {
                    Ok(boxparexpr!(ParenExpression::Lambda { arg, body }))
                } else {
                    bail!(
                        "Something went wrong internally; a lambdas first term \
                         must be an identifier."
                    )
                }
            }
            Token::Binding => {
                if self.terms.len() != 3 {
                    bail!(
                        "Something went wrong internally; tried to build a binding \
                         with {} terms instead of 3.",
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
                        "Something went wrong internally; a bindings first term \
                         must be an identifier."
                    )
                }
            }
            Token::Cons => {
                if self.terms.len() != 2 {
                    bail!(
                        "Something went wrong internally; tried to build a cons expression \
                         with {} terms instead of 2.",
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
                        "Something went wrong internally; tried to build a car expression \
                         with {} terms instead of 1.",
                        self.terms.len()
                    )
                }
                let cons = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Car { cons }))
            }
            Token::Cdr => {
                if self.terms.len() != 1 {
                    bail!(
                        "Something went wrong internally; tried to build a cdr expression \
                         with {} terms instead of 1.",
                        self.terms.len()
                    )
                }
                let cons = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::Cdr { cons }))
            }
            Token::NullCheck => {
                if self.terms.len() != 1 {
                    bail!(
                        "Something went wrong internally; tried to build a null check expression \
                         with {} terms instead of 1.",
                        self.terms.len()
                    )
                }
                let value = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::NullCheck { value }))
            }
            Token::LessThan => {
                build_two_arg_parexpr!(self.terms, LessThan)
            }
            Token::GreaterThan => {
                build_two_arg_parexpr!(self.terms, GreaterThan)
            }
            Token::LogicalAnd => {
                build_two_arg_parexpr!(self.terms, LogicalAnd)
            }
            Token::LogicalOr => {
                build_two_arg_parexpr!(self.terms, LogicalOr)
            }
            Token::LogicalNot => {
                if self.terms.len() != 1 {
                    bail!(
                        "Something went wrong internally; tried to build a logical \"not\" expression \
                         with {} terms instead of 1.",
                        self.terms.len()
                    )
                }
                let value = self.terms.pop().unwrap();
                Ok(boxparexpr!(ParenExpression::LogicalNot { value }))
            }
            Token::RightParen | Token::Null | Token::Number(_) => bail!(
                "Something went wrong internally; can't finish a paren expression \
                 that started with a right parenthesis or a wildcard.",
            ),
        }
    }

    pub fn finished(&self) -> bool {
        self.terms_finished
    }
}

#[derive(Debug)]
pub enum Builder {
    Expr(ExprBuilder),
    Paren(ParenExprBuilder),
}

/// Generic interface for building a composite form.
impl Builder {
    /// Add an expression to the expression we are building.
    pub fn take(&mut self, expr: BoxExpr) -> Result<()> {
        match self {
            Self::Expr(expr_builder) => expr_builder.take(expr),
            Self::Paren(parexpr_builder) => parexpr_builder.take(expr),
        }
    }

    /// Consume the builder and return the finished expression.
    pub fn build(&mut self) -> Result<BoxExpr> {
        match self {
            Self::Expr(expr_builder) => expr_builder.build(),
            Self::Paren(parexpr_builder) => parexpr_builder.build(),
        }
    }

    /// Is the builder ready to be consumed?
    pub fn finished(&self) -> bool {
        match self {
            Self::Expr(expr_builder) => expr_builder.finished(),
            Self::Paren(parexpr_builder) => parexpr_builder.finished(),
        }
    }
}
