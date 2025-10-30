#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    LeftParen,
    RightParen,
    Number(usize),
    Identifier(String),
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

type BoxExpr = Box<Expression>;
type BoxParenExpr = Box<ParenExpression>;

#[derive(Debug, PartialEq, Eq)]
pub enum Expression {
    Number(usize),
    Identifier(String),
    ParenExpression(BoxParenExpr),
    Null,
}

#[derive(Debug, PartialEq, Eq)]
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
    Exprs(Vec<BoxExpr>),
}
