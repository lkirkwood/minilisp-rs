use anyhow::{bail, Result};

use crate::model::Token;

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
            '(' => tokens.push(Token::LeftParen),
            '0'..='9' => {
                if let Some(BufferedType::Identifier) = buf_type {
                    bail!("Numeric character in token that started as an identifier: {character}")
                }
                buf_type = Some(BufferedType::Number);
                char_buf.push(character);
            }
            'a'..='z' | '-' | '_' => {
                if let Some(BufferedType::Number) = buf_type {
                    bail!(
                        "Identifier-class character in token that started as a number: {character}"
                    )
                }
                buf_type = Some(BufferedType::Identifier);
                char_buf.push(character);
            }
            ')' => {
                flush_char_buf(&mut buf_type, &mut char_buf, &mut tokens);
                tokens.push(Token::RightParen)
            }
            ' ' | '\t' | '\n' => {
                flush_char_buf(&mut buf_type, &mut char_buf, &mut tokens);
            }
            '+' => tokens.push(Token::Plus),
            '−' => tokens.push(Token::Minus),
            '×' => tokens.push(Token::Times),
            '=' => tokens.push(Token::Equals),
            '?' => tokens.push(Token::Condition),
            'λ' => tokens.push(Token::Lambda),
            '≜' => tokens.push(Token::Binding),
            _ => bail!("Unexpected character: {character}"),
        }
    }

    flush_char_buf(&mut buf_type, &mut char_buf, &mut tokens);

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

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
            tokenise("(≜ myident (× 42 100))").unwrap(),
            vec![
                Token::LeftParen,
                Token::Binding,
                Token::Identifier("myident".to_string()),
                Token::LeftParen,
                Token::Times,
                Token::Number(42),
                Token::Number(100),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn tokenise_number() {
        assert_eq!(tokenise("42").unwrap(), vec![Token::Number(42)]);
    }

    #[test]
    fn tokenise_invalid_char() {
        assert!(tokenise("(⌒)").is_err());
    }
}
