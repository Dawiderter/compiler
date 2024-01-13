use std::ops::Range;
use std::str::FromStr;

use line_span::LineSpanExt;
use owo_colors::OwoColorize;
use winnow::ascii::{digit1, multispace0};
use winnow::combinator::{alt, fail, fold_repeat, peek, preceded, terminated};
use winnow::token::{any, take_till, take_while};
use winnow::{dispatch, Located};
use winnow::{PResult, Parser};

pub type LexingStream<'a> = Located<&'a str>;

#[rustfmt::skip]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    PIdent(String),
    Num(u64),
    T,
    OpenBrace, CloseBrace,
    OpenParen, CloseParen,
    MathOperator(MathOperator),
    CondOperator(CondOperator),
    Assign,
    SemiColon, Comma,
    Space,
    If, Then, Else, Endif,
    While, Do, Endwhile,
    Repeat, Until,
    Read, Write,
    Program, Procedure, Is, In, End,
    Comment,
    Error,
}

#[rustfmt::skip]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MathOperator {
    Add, Sub, Mul, Div, Rem,
}

#[rustfmt::skip]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CondOperator {
    Equal, NotEqual, Greater, Lesser, GreaterEq, LesserEq,
}

impl CondOperator {
    pub fn negate(self) -> CondOperator {
        match self {
            CondOperator::Equal => CondOperator::NotEqual,
            CondOperator::NotEqual => CondOperator::Equal,
            CondOperator::Greater => CondOperator::LesserEq,
            CondOperator::Lesser => CondOperator::GreaterEq,
            CondOperator::GreaterEq => CondOperator::Lesser,
            CondOperator::LesserEq => CondOperator::Greater,
        }
    }
}

impl winnow::stream::ContainsToken<Token> for Token {
    #[inline(always)]
    fn contains_token(&self, token: Token) -> bool {
        *self == token
    }
}

#[derive(Debug, Clone, Default)]
pub struct LexResult {
    pub tokens: Vec<Token>,
    pub spans: Vec<Range<usize>>,
    pub errors: Vec<Range<usize>>,
}

pub fn report_lex_errors(i: &str, errors: &[Range<usize>]) {
    let mut lines = i.line_spans();
    let mut line_number = 0;

    for error in errors {
        for lin in lines.by_ref() {
            line_number += 1;
            if lin.range().contains(&error.start) {
                println!("Unexpected token on line {}: {}{}{}", line_number.bold(), &i[lin.start()..error.start],(&i[error.start..error.end]).bold().red() ,&i[error.end..lin.end()]);

                break;
            }
        };
    }
}

pub fn lex_str(i: &str) -> LexResult {
    let stream = Located::new(i);
    lex.parse(stream).unwrap()
}

pub fn lex(i: &mut LexingStream) -> PResult<LexResult> {
    preceded(
        multispace0,
        fold_repeat(
            0..,
            terminated(token_type.with_span(), multispace0),
            LexResult::default,
            |mut lexer, (typ, span)| {
                match typ {
                    Token::Comment => {}
                    Token::Error => lexer.errors.push(span),
                    _ => {
                        lexer.tokens.push(typ);
                        lexer.spans.push(span);
                    }
                }
                lexer
            },
        ),
    )
    .parse_next(i)
}

fn comment(i: &mut LexingStream) -> PResult<()> {
    ('#', take_till(0.., ['\n', '\r'])).void().parse_next(i)
}

fn token_type(i: &mut LexingStream) -> PResult<Token> {
    alt((
        dispatch! {peek(any);
            '0'..='9' => digit1.try_map(FromStr::from_str).map(Token::Num),
            'a'..='z' | '_' => take_while(1.., |c: char| c.is_ascii_lowercase() || c == '_').map(|s: &str| Token::PIdent(s.to_owned())),
            '(' => '('.value(Token::OpenParen),
            ')' => ')'.value(Token::CloseParen),
            '[' => '['.value(Token::OpenBrace),
            ']' => ']'.value(Token::CloseBrace),
            '+' => '+'.value(Token::MathOperator(MathOperator::Add)),
            '-' => '-'.value(Token::MathOperator(MathOperator::Sub)),
            '*' => '*'.value(Token::MathOperator(MathOperator::Mul)),
            '/' => '/'.value(Token::MathOperator(MathOperator::Div)),
            '%' => '%'.value(Token::MathOperator(MathOperator::Rem)),
            '=' => '='.value(Token::CondOperator(CondOperator::Equal)),
            '!' => "!=".value(Token::CondOperator(CondOperator::NotEqual)),
            '>' => alt((">=".value(Token::CondOperator(CondOperator::GreaterEq)), '>'.value(Token::CondOperator(CondOperator::Greater)))),
            '<' => alt(("<=".value(Token::CondOperator(CondOperator::LesserEq)), '<'.value(Token::CondOperator(CondOperator::Lesser)))),
            ',' => ','.value(Token::Comma),
            ';' => ';'.value(Token::SemiColon),
            ':' => ":=".value(Token::Assign),
            '#' => comment.value(Token::Comment),
            'D' => "DO".value(Token::Do),
            'E' => alt(("ENDIF".value(Token::Endif),"ENDWHILE".value(Token::Endwhile),"END".value(Token::End), "ELSE".value(Token::Else))),
            'I' => alt(("IF".value(Token::If),"IS".value(Token::Is),"IN".value(Token::In))),
            'P' => alt(("PROCEDURE".value(Token::Procedure),"PROGRAM".value(Token::Program))),
            'R' => alt(("REPEAT".value(Token::Repeat), "READ".value(Token::Read))),
            'T' => alt(("THEN".value(Token::Then),"T".value(Token::T))),
            'U' => "UNTIL".value(Token::Until),
            'W' => alt(("WHILE".value(Token::While), "WRITE".value(Token::Write))),
            _ => fail,
        },
        take_till(1.., (' ', '\t', '\r', '\n')).value(Token::Error)
    ))
    .parse_next(i)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let input = include_str!("../examples2023/example1.imp");
        let stream = Located::new(input);
        let res = lex.parse(stream).unwrap();

        if !res.errors.is_empty() {
            report_lex_errors(input, &res.errors);
        }
    }
}
