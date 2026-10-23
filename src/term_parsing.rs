use std::{iter::Peekable, str::Chars};

use color_print::cprintln;
use itertools::Itertools;
use thiserror::Error;

use crate::{reduction::{beta_reduce, normal_order_reduction}, term_representation::{CanonicalTerm, Name, TermRepresentation}};

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ParseErr {
    #[error("no tokens")]
    NoTokens,
    #[error("unexpected eof")]
    UnexpectedEof,
    #[error("expected {0:?}, got {1:?}")]
    ExpectedSpecificToken(Token, Option<Token>),
    #[error("any of: {0:?}")]
    Any(Vec<ParseErr>),
    #[error("bad modifier: {0:?}")]
    BadModifier(ParsedModifier),
}

pub fn parse_term(source: &str) -> Result<CanonicalTerm, ParseErr> {
    let tokens = Lexer::new(source).collect_vec();
    if tokens.is_empty() {
        Err(ParseErr::NoTokens)
    } else {
        parse_term_root(Parser::new(&tokens)).map(|(_, term)| term)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Unknown(char),
    Name(Name),
    Lambda,
    Dot,
    OpenParen,
    CloseParen,
    Bang,
}

struct Lexer<'source> {
    chars: Peekable<Chars<'source>>,
}

impl<'source> Lexer<'source> {
    fn new(source: &'source str) -> Self {
        Self {
            chars: source.chars().peekable(),
        }
    }

    fn eat_char(&mut self, c: char) -> bool {
        if self.chars.peek().copied() == Some(c) {
            self.chars.next();
            true
        } else {
            false
        }
    }

    // word = [a-zA-Z0-9]*
    fn eat_word(&mut self) -> Option<String> {
        if self.chars.peek().is_none_or(|c| !c.is_alphanumeric()) {
            return None;
        }
        let mut w = String::new();
        while let Some(&c) = self.chars.peek()
            && c.is_alphanumeric()
        {
            w.push(c);
            self.chars.next();
        }
        Some(w)
    }

    fn skip_whitespace(&mut self) {
        while self.chars.peek().is_some_and(|c| c.is_whitespace()) {
            self.chars.next();
        }
    }
}

impl<'source> Iterator for Lexer<'source> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespace();

        // If we see a comment, stop tokenizing the line.
        if self.eat_char('#') {
            return None;
        }

        // Char tokens.
        for (c, token) in [
            ('λ', Token::Lambda),
            ('\\', Token::Lambda),
            ('.', Token::Dot),
            ('(', Token::OpenParen),
            (')', Token::CloseParen),
            ('!', Token::Bang),
        ]
        .into_iter()
        {
            if self.eat_char(c) {
                return Some(token.clone());
            }
        }

        // Word
        if let Some(w) = self.eat_word() {
            return Some(Token::Name(Name::from(w)));
        }

        self.chars.next().map(|c| Token::Unknown(c))
    }
}

#[derive(Clone, Debug)]
struct Parser<'tokens> {
    tokens: &'tokens [Token],
}

impl<'tokens> Parser<'tokens> {
    fn new(tokens: &'tokens [Token]) -> Self {
        Self { tokens }
    }

    fn peek(&mut self) -> Result<&Token, ParseErr> {
        self.tokens.get(0).ok_or(ParseErr::UnexpectedEof)
    }

    fn next(&mut self) -> Result<(), ParseErr> {
        if self.tokens.is_empty() {
            Err(ParseErr::UnexpectedEof)
        } else {
            self.tokens = &self.tokens[1..];
            Ok(())
        }
    }

    fn accept(&mut self, token: &Token) -> bool {
        if self.peek().is_ok_and(|t| t == token) {
            self.next()
                .expect("as peek() == token we should not be at the eof");
            true
        } else {
            false
        }
    }

    fn expect(&mut self, token: &Token) -> Result<(), ParseErr> {
        if self.accept(token) {
            Ok(())
        } else {
            Err(ParseErr::ExpectedSpecificToken(
                token.clone(),
                self.peek().ok().cloned(),
            ))
        }
    }
}

fn parse_variable(mut parser: Parser) -> Result<(Parser, CanonicalTerm), ParseErr> {
    match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok((parser.clone(), CanonicalTerm::Variable(name.clone())))
        }
        _ => Err(ParseErr::ExpectedSpecificToken(
            Token::Name(Name::from("")),
            parser.peek().ok().cloned(),
        )),
    }
}
fn parse_abstraction(mut parser: Parser) -> Result<(Parser, CanonicalTerm), ParseErr> {
    // We support the shorthand \x y z. insteaad of \x.\y.\z.

    // Lambda.
    parser.expect(&Token::Lambda)?;

    // Argument.
    let mut args = vec![match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok(name.clone())
        }
        _ => Err(ParseErr::ExpectedSpecificToken(
            Token::Name(Name::from("")),
            parser.peek().ok().cloned(),
        )),
    }?];

    // moar args
    loop {
        let Ok(Token::Name(name)) = parser.peek().cloned() else {
            break;
        };
        parser.next()?;
        args.push(name);
    }

    parser.expect(&Token::Dot)?;

    let (parser, body) = parse_term_root(parser.clone())?;

    let mut term = body;
    for arg in args.into_iter().rev() {
        term = CanonicalTerm::Abstraction(arg, Box::new(term));
    }

    Ok((parser, term))
}

fn parse_application(parser: Parser) -> Result<(Parser, CanonicalTerm), ParseErr> {
    // Applications are left associative by convention.
    // As the parser is LL, handling applications by recursion
    // leads to infinite left recursion. So we find all atoms
    // using a loop and then construct the left associative parse tree.
    let (mut parser, mut term) = parse_atom(parser)?;
    while ![Ok(Token::CloseParen), Err(ParseErr::UnexpectedEof)]
        .into_iter()
        .contains(&parser.peek().cloned())
    {
        let (new_parser, new_term) = parse_atom(parser.clone())?;
        parser = new_parser;
        term = CanonicalTerm::Application(Box::new(term), Box::new(new_term));
    }

    Ok((parser, term))
}

fn parse_modifier(mut parser: Parser) -> Result<(Parser, ParsedModifier), ParseErr> {
    let name = match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok(name.clone())
        }
        _ => Err(ParseErr::ExpectedSpecificToken(
            Token::Name(Name::from("")),
            parser.peek().ok().cloned(),
        )),
    }?;

    parser.expect(&Token::Bang)?;

    parser.expect(&Token::OpenParen)?;

    let mut args = vec![];
    while !parser.accept(&Token::CloseParen) {
        let (new_parser, term) = parse_term_root(parser)?;
        args.push(term);
        parser = new_parser;
    }

    Ok((parser, ParsedModifier { name, args }))
}

fn parse_parenthesised_term(mut parser: Parser) -> Result<(Parser, CanonicalTerm), ParseErr> {
    parser.expect(&Token::OpenParen)?;
    let (mut parser, term) = parse_term_root(parser.clone())?;
    parser.expect(&Token::CloseParen)?;
    return Ok((parser, term));
}

fn parse_atom(parser: Parser) -> Result<(Parser, CanonicalTerm), ParseErr> {
    let mut errors = Vec::new();

    match parse_modifier(parser.clone()) {
        Ok((parser, parsed_modifier)) => {
            let term = Modifier::from_parsed(parsed_modifier.clone())
                .ok_or(ParseErr::BadModifier(parsed_modifier))?
                .apply();
            return Ok((parser, term));
        }
        Err(e) => errors.push(e),
    }

    match parse_parenthesised_term(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    match parse_variable(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    Err(ParseErr::Any(errors))
}

fn parse_abstractive_term(parser: Parser) -> Result<(Parser, CanonicalTerm), ParseErr> {
    let mut errors = Vec::new();

    match parse_abstraction(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    match parse_application(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    Err(ParseErr::Any(errors))
}

fn parse_term_root(parser: Parser) -> Result<(Parser, CanonicalTerm), ParseErr> {
    let mut errors = Vec::new();

    match parse_abstractive_term(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    Err(ParseErr::Any(errors))
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedModifier {
    name: Name,
    args: Vec<CanonicalTerm>,
}

#[derive(Clone, Debug)]
enum Modifier {
    Subst(Name, CanonicalTerm, CanonicalTerm),
    BetaReduce(CanonicalTerm),
    NormalOrderReduce(CanonicalTerm),
    ChurchNumeral(num_bigint::BigUint),
}

impl Modifier {
    fn from_parsed(parsed: ParsedModifier) -> Option<Modifier> {
        match parsed.name.as_str() {
            "subst" => {
                if parsed.args.len() != 3 {
                    return None;
                }
                let mut it = parsed.args.into_iter();
                let CanonicalTerm::Variable(name) = it.next().unwrap() else {
                    return None;
                };

                Some(Self::Subst(name, it.next().unwrap(), it.next().unwrap()))
            }
            "bred" => {
                if parsed.args.len() != 1 {
                    None
                } else {
                    Some(Self::BetaReduce(parsed.args.into_iter().next().unwrap()))
                }
            }
            "nor" => {
                if parsed.args.len() != 1 {
                    None
                } else {
                    Some(Self::NormalOrderReduce(
                        parsed.args.into_iter().next().unwrap(),
                    ))
                }
            }
            "cnum" => {
                if parsed.args.len() != 1 {
                    None
                } else {
                    let CanonicalTerm::Variable(name) = parsed.args.into_iter().next()? else {
                        return None;
                    };
                    Some(Self::ChurchNumeral(name.as_str().parse().ok()?))
                }
            }
            _ => None,
        }
    }

    fn apply(self) -> CanonicalTerm {
        match self {
            Self::Subst(name, substituted, mut term) => {
                term.substitute(&name, &substituted);
                term
            }
            Self::BetaReduce(mut term) => {
                beta_reduce(&mut term);
                term
            }
            Self::NormalOrderReduce(mut term) => {
                normal_order_reduction(&mut term);
                term
            }
            Self::ChurchNumeral(value) => CanonicalTerm::create_church_numeral(value),
        }
    }
}
