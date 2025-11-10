use crate::tokeniser::Token;
use std::{collections::HashMap, sync::LazyLock};

/// Terminal stack symbols - just the tags from the Token tagged union.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Terminal {
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
    LessThan,
    GreaterThan,
    LogicalAnd,
    LogicalOr,
    LogicalNot,
    Match,
    Wildcard,
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
            Token::LessThan => Self::LessThan,
            Token::GreaterThan => Self::GreaterThan,
            Token::LogicalAnd => Self::LogicalAnd,
            Token::LogicalOr => Self::LogicalOr,
            Token::LogicalNot => Self::LogicalNot,
            Token::Match => Self::Match,
            Token::Wildcard => Self::Wildcard,
        }
    }
}

/// Non-terminal stack symbols.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum NonTerminal {
    Expression,
    ParenExpression,
    PatternClauses,
    Epsilon,
    End,
}

/// Parser stack symbols.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum StackSymbol {
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

/// The LL(1) transition table.
pub static TRANSITION_TABLE: LazyLock<HashMap<(Terminal, NonTerminal), Vec<StackSymbol>>> =
    LazyLock::new(|| {
        HashMap::from([
            // expression -> number
            (
                (Terminal::Number, NonTerminal::Expression),
                vec![term!(Number)],
            ),
            // expression -> identifier
            (
                (Terminal::Identifier, NonTerminal::Expression),
                vec![term!(Identifier)],
            ),
            // expression -> null
            ((Terminal::Null, NonTerminal::Expression), vec![term!(Null)]),
            // expression -> wildcard
            (
                (Terminal::Wildcard, NonTerminal::Expression),
                vec![term!(Wildcard)],
            ),
            // expression -> paren expression
            (
                (Terminal::LeftParen, NonTerminal::Expression),
                vec![
                    term!(LeftParen),
                    nonterm!(ParenExpression),
                    term!(RightParen),
                ],
            ),
            // paren expression -> plus
            (
                (Terminal::Plus, NonTerminal::ParenExpression),
                vec![term!(Plus), nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> minus
            (
                (Terminal::Minus, NonTerminal::ParenExpression),
                vec![term!(Minus), nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> times
            (
                (Terminal::Times, NonTerminal::ParenExpression),
                vec![term!(Times), nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> equals
            (
                (Terminal::Equals, NonTerminal::ParenExpression),
                vec![term!(Equals), nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> condition
            (
                (Terminal::Condition, NonTerminal::ParenExpression),
                vec![
                    term!(Condition),
                    nonterm!(Expression),
                    nonterm!(Expression),
                    nonterm!(Expression),
                ],
            ),
            // paren expression -> lambda
            (
                (Terminal::Lambda, NonTerminal::ParenExpression),
                vec![term!(Lambda), term!(Identifier), nonterm!(Expression)],
            ),
            // paren expression -> binding
            (
                (Terminal::Binding, NonTerminal::ParenExpression),
                vec![
                    term!(Binding),
                    term!(Identifier),
                    nonterm!(Expression),
                    nonterm!(Expression),
                ],
            ),
            // paren expression -> cons
            (
                (Terminal::Cons, NonTerminal::ParenExpression),
                vec![term!(Cons), nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> car
            (
                (Terminal::Car, NonTerminal::ParenExpression),
                vec![term!(Car), nonterm!(Expression)],
            ),
            // paren expression -> cdr
            (
                (Terminal::Cdr, NonTerminal::ParenExpression),
                vec![term!(Cdr), nonterm!(Expression)],
            ),
            // paren expression -> nullcheck
            (
                (Terminal::NullCheck, NonTerminal::ParenExpression),
                vec![term!(NullCheck), nonterm!(Expression)],
            ),
            // paren expression -> less than
            (
                (Terminal::LessThan, NonTerminal::ParenExpression),
                vec![term!(LessThan), nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> greater than
            (
                (Terminal::GreaterThan, NonTerminal::ParenExpression),
                vec![
                    term!(GreaterThan),
                    nonterm!(Expression),
                    nonterm!(Expression),
                ],
            ),
            // paren expression -> logical and
            (
                (Terminal::LogicalAnd, NonTerminal::ParenExpression),
                vec![
                    term!(LogicalAnd),
                    nonterm!(Expression),
                    nonterm!(Expression),
                ],
            ),
            // paren expression -> logical or
            (
                (Terminal::LogicalOr, NonTerminal::ParenExpression),
                vec![term!(LogicalOr), nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> logical not
            (
                (Terminal::LogicalNot, NonTerminal::ParenExpression),
                vec![term!(LogicalNot), nonterm!(Expression)],
            ),
            // paren expression -> application
            (
                (Terminal::Identifier, NonTerminal::ParenExpression),
                vec![nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> application
            (
                (Terminal::LeftParen, NonTerminal::ParenExpression),
                vec![nonterm!(Expression), nonterm!(Expression)],
            ),
            // paren expression -> match
            (
                (Terminal::Match, NonTerminal::ParenExpression),
                vec![term!(Match), nonterm!(Expression), nonterm!(PatternClauses)],
            ),
            // pattern clauses -> pattern
            (
                (Terminal::LeftParen, NonTerminal::PatternClauses),
                vec![
                    term!(LeftParen),
                    nonterm!(Expression),
                    nonterm!(Expression),
                    term!(RightParen),
                    nonterm!(PatternClauses),
                ],
            ),
            // pattern clauses -> pattern clause
            (
                (Terminal::RightParen, NonTerminal::PatternClauses),
                vec![nonterm!(Epsilon)],
            ),
        ])
    });
