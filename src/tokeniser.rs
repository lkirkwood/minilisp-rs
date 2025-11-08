use anyhow::{Result, bail};

#[derive(Debug, PartialEq, Eq, Clone)]
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
    LessThan,
    GreaterThan,
    LogicalAnd,
    LogicalOr,
    LogicalNot,
    Match,
    Wildcard,
}

enum BufferedType {
    Number,
    Identifier,
}

/// Parse the contents of the character buffer into a token and add them to the list of tokens, if necessary.
/// Cleans up after itself by flushing character buffer and resetting buffered type to None.
fn flush_char_buf(
    buf_type: &mut Option<BufferedType>,
    char_buf: &mut Vec<char>,
    tokens: &mut Vec<Token>,
) {
    if let Some(BufferedType::Number) = buf_type {
        let mut number = 0;
        for num_char in char_buf.iter() {
            number *= 10;
            number += (*num_char as usize) - 48;
        }
        tokens.push(Token::Number(number));
    } else if let Some(BufferedType::Identifier) = buf_type {
        tokens.push(Token::Identifier(char_buf.iter().collect()));
    }
    *buf_type = None;
    char_buf.clear();
}

/// Tokenise a program string.
pub fn tokenise(program_string: &str) -> Result<Vec<Token>> {
    let mut char_buf = Vec::new();
    let mut buf_type: Option<BufferedType> = None;
    let mut tokens = Vec::new();

    for character in program_string.chars() {
        match character {
            ')' => {
                flush_char_buf(&mut buf_type, &mut char_buf, &mut tokens);
                tokens.push(Token::RightParen);
            }
            ' ' | '\t' | '\n' => {
                flush_char_buf(&mut buf_type, &mut char_buf, &mut tokens);
            }
            '(' => tokens.push(Token::LeftParen),
            '+' => tokens.push(Token::Plus),
            '−' => tokens.push(Token::Minus),
            '×' => tokens.push(Token::Times),
            '=' => tokens.push(Token::Equals),
            '?' => tokens.push(Token::Condition),
            'λ' => tokens.push(Token::Lambda),
            '≜' => tokens.push(Token::Binding),
            '∅' => tokens.push(Token::Null),
            '∷' => tokens.push(Token::Cons),
            '←' => tokens.push(Token::Car),
            '→' => tokens.push(Token::Cdr),
            '∘' => tokens.push(Token::NullCheck),
            '‹' => tokens.push(Token::LessThan),
            '›' => tokens.push(Token::GreaterThan),
            '∧' => tokens.push(Token::LogicalAnd),
            '∨' => tokens.push(Token::LogicalOr),
            '¬' => tokens.push(Token::LogicalNot),
            '⊢' => tokens.push(Token::Match),
            '_' => tokens.push(Token::Wildcard),
            '0'..='9' => {
                if let Some(BufferedType::Identifier) = buf_type {
                    bail!("Numeric character in token that started as an identifier: {character}")
                }
                buf_type = Some(BufferedType::Number);
                char_buf.push(character);
            }
            _ => {
                if let Some(BufferedType::Number) = buf_type {
                    bail!(
                        "Identifier-class character in token that started as a number: {character}"
                    )
                }
                buf_type = Some(BufferedType::Identifier);
                char_buf.push(character);
            }
        }
    }

    flush_char_buf(&mut buf_type, &mut char_buf, &mut tokens);

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenise_number() {
        assert_eq!(tokenise("42").unwrap(), vec![Token::Number(42)]);
    }

    #[test]
    fn tokenise_addition() {
        assert_eq!(
            tokenise("(+ 123 456)").unwrap(),
            vec![
                Token::LeftParen,
                Token::Plus,
                Token::Number(123),
                Token::Number(456),
                Token::RightParen
            ]
        );
    }

    #[test]
    fn tokenise_arithmetic() {
        assert_eq!(
            tokenise("(+ (× 1 42) (− 42 0))").unwrap(),
            vec![
                Token::LeftParen,
                Token::Plus,
                Token::LeftParen,
                Token::Times,
                Token::Number(1),
                Token::Number(42),
                Token::RightParen,
                Token::LeftParen,
                Token::Minus,
                Token::Number(42),
                Token::Number(0),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn tokenise_binding() {
        assert_eq!(
            tokenise("(≜ x 10 (+ x x)) ").unwrap(),
            vec![
                Token::LeftParen,
                Token::Binding,
                Token::Identifier("x".to_string()),
                Token::Number(10),
                Token::LeftParen,
                Token::Plus,
                Token::Identifier("x".to_string()),
                Token::Identifier("x".to_string()),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn tokenise_lists() {
        assert_eq!(
            tokenise("(≜ lst (∷ 42 (∷ 99 ∅)) (∨ (∘ (← lst)) (∘ (→ (→ lst)))))").unwrap(),
            vec![
                Token::LeftParen,
                Token::Binding,
                Token::Identifier("lst".to_string()),
                Token::LeftParen,
                Token::Cons,
                Token::Number(42),
                Token::LeftParen,
                Token::Cons,
                Token::Number(99),
                Token::Null,
                Token::RightParen,
                Token::RightParen,
                Token::LeftParen,
                Token::LogicalOr,
                Token::LeftParen,
                Token::NullCheck,
                Token::LeftParen,
                Token::Car,
                Token::Identifier("lst".to_string()),
                Token::RightParen,
                Token::RightParen,
                Token::LeftParen,
                Token::NullCheck,
                Token::LeftParen,
                Token::Cdr,
                Token::LeftParen,
                Token::Cdr,
                Token::Identifier("lst".to_string()),
                Token::RightParen,
                Token::RightParen,
                Token::RightParen,
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn tokenise_invalid_ident() {
        assert!(tokenise("(≜ lst99 (∷ 42 ∅))").is_err());
    }

    #[test]
    fn tokenise_invalid_number() {
        assert!(tokenise("(≜ lst (∷ 42abc ∅))").is_err());
    }
}
