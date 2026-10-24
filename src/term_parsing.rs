use std::str::Chars;

use itertools::{Itertools, PeekNth, peek_nth};
use thiserror::Error;

use crate::{
    reduction::{beta_reduce, normal_order_reduction},
    term_representation::{CanonicalTerm, Name, TermRepresentation},
    type_system::IsTypeSystem,
};

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ParseError {
    /// Error returned when attempting to parse something that doesn't exist, for
    /// example a constant in the untyped lambda calculus.
    #[error("doesn't exist")]
    DoesntExist,
    /// Error returned when the input token stream is empty.
    #[error("no tokens")]
    NoTokens,
    #[error("unexpected eof")]
    UnexpectedEof,
    #[error("expected {0:?}, got {1:?}")]
    ExpectedSpecificToken(Token, Option<Token>),
    #[error("any of: {0:?}")]
    Any(Vec<ParseError>),
    #[error("bad modifier")]
    BadModifier,
    #[error("{0}")]
    Other(String),
}

pub fn parse_term<TypeSystem: IsTypeSystem>(
    source: &str,
) -> Result<CanonicalTerm<TypeSystem>, ParseError> {
    let tokens = Lexer::new(source).collect_vec();
    log::trace!("Tokens: {tokens:?}");
    if tokens.is_empty() {
        Err(ParseError::NoTokens)
    } else {
        parse_term_root(Parser::new(&tokens)).map(|(_, term)| term)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Unknown(char),
    Name(Name),
    Lambda,
    Dot,
    OpenParen,
    CloseParen,
    Colon,
    Arrow,
    Bang,
    Comma,
}

struct Lexer<'source> {
    chars: PeekNth<Chars<'source>>,
}

impl<'source> Lexer<'source> {
    fn new(source: &'source str) -> Self {
        Self {
            chars: peek_nth(source.chars()),
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

    fn eat_str(&mut self, s: &str) -> bool {
        for (i, c) in s.chars().enumerate() {
            if self.chars.peek_nth(i).copied() != Some(c) {
                return false;
            }
        }
        for _ in 0..s.len() {
            self.chars.next();
        }
        true
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
        while self
            .chars
            .peek()
            .is_some_and(|&c| c.is_whitespace() || c == '_')
        {
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

        // Simple tokens.
        for (s, token) in [
            ("->", Token::Arrow),
            ("λ", Token::Lambda),
            ("\\", Token::Lambda),
            (".", Token::Dot),
            ("(", Token::OpenParen),
            (")", Token::CloseParen),
            (":", Token::Colon),
            ("!", Token::Bang),
            (",", Token::Comma),
        ]
        .into_iter()
        {
            if self.eat_str(s) {
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
pub struct Parser<'tokens> {
    tokens: &'tokens [Token],
}

impl<'tokens> Parser<'tokens> {
    pub fn new(tokens: &'tokens [Token]) -> Self {
        Self { tokens }
    }

    pub fn peek(&mut self) -> Result<&Token, ParseError> {
        self.tokens.get(0).ok_or(ParseError::UnexpectedEof)
    }

    pub fn next(&mut self) -> Result<(), ParseError> {
        if self.tokens.is_empty() {
            Err(ParseError::UnexpectedEof)
        } else {
            self.tokens = &self.tokens[1..];
            Ok(())
        }
    }

    pub fn accept(&mut self, token: &Token) -> bool {
        if self.peek().is_ok_and(|t| t == token) {
            self.next()
                .expect("as peek() == token we should not be at the eof");
            true
        } else {
            false
        }
    }

    pub fn expect(&mut self, token: &Token) -> Result<(), ParseError> {
        if self.accept(token) {
            Ok(())
        } else {
            Err(ParseError::ExpectedSpecificToken(
                token.clone(),
                self.peek().ok().cloned(),
            ))
        }
    }
}

fn parse_variable<TypeSystem>(
    mut parser: Parser,
) -> Result<(Parser, CanonicalTerm<TypeSystem>), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok((parser.clone(), CanonicalTerm::Variable(name.clone())))
        }
        _ => Err(ParseError::ExpectedSpecificToken(
            Token::Name(Name::from("")),
            parser.peek().ok().cloned(),
        )),
    }
}

fn parse_arg<TypeSystem>(
    mut parser: Parser,
) -> Result<(Parser, (Name, Option<TypeSystem::Type>)), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    let name = match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok(name.clone())
        }
        _ => Err(ParseError::ExpectedSpecificToken(
            Token::Name(Name::from("")),
            parser.peek().ok().cloned(),
        )),
    }?;

    let ty = if parser.accept(&Token::Colon) {
        let (new_parser, ty) = TypeSystem::Type::parse(parser)?;
        parser = new_parser;
        Some(ty)
    } else {
        None
    };

    Ok((parser, (name, ty)))
}

fn parse_abstraction<TypeSystem>(
    mut parser: Parser,
) -> Result<(Parser, CanonicalTerm<TypeSystem>), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    // We support the shorthand \x y z. insteaad of \x.\y.\z.

    // Lambda.
    parser.expect(&Token::Lambda)?;

    // Argument.
    let (new_parser, arg) = parse_arg::<TypeSystem>(parser)?;
    parser = new_parser;
    let mut args = vec![arg];

    // moar args
    loop {
        let Ok(Token::Name(_)) = parser.peek().cloned() else {
            break;
        };

        let (new_parser, arg) = parse_arg::<TypeSystem>(parser)?;
        parser = new_parser;
        args.push(arg);
    }

    parser.expect(&Token::Dot)?;

    let (parser, body) = parse_term_root(parser.clone())?;

    let mut term = body;
    for (name, ty) in args.into_iter().rev() {
        term = CanonicalTerm::Abstraction(name, Box::new(term), ty);
    }

    Ok((parser, term))
}

fn parse_application<TypeSystem>(
    parser: Parser,
) -> Result<(Parser, CanonicalTerm<TypeSystem>), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    // Applications are left associative by convention.
    // As the parser is LL, handling applications by recursion
    // leads to infinite left recursion. So we find all atoms
    // using a loop and then construct the left associative parse tree.
    let (mut parser, mut term) = parse_atom(parser)?;
    while ![
        Ok(Token::CloseParen),
        Ok(Token::Comma),
        Err(ParseError::UnexpectedEof),
    ]
    .into_iter()
    .contains(&parser.peek().cloned())
    {
        let (new_parser, new_term) = parse_atom(parser.clone())?;
        parser = new_parser;
        term = CanonicalTerm::Application(Box::new(term), Box::new(new_term));
    }

    Ok((parser, term))
}

fn parse_modifier<TypeSystem>(
    mut parser: Parser,
) -> Result<(Parser, ParsedModifier<TypeSystem>), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    let name = match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok(name.clone())
        }
        _ => Err(ParseError::ExpectedSpecificToken(
            Token::Name(Name::from("")),
            parser.peek().ok().cloned(),
        )),
    }?;

    parser.expect(&Token::Bang)?;

    parser.expect(&Token::OpenParen)?;

    let mut args = vec![];
    while !parser.accept(&Token::CloseParen) {
        if !args.is_empty() {
            parser.expect(&Token::Comma)?;
        }

        let (new_parser, term) = parse_term_root(parser)?;
        args.push(term);
        parser = new_parser;
    }

    Ok((parser, ParsedModifier { name, args }))
}

fn parse_parenthesised_term<TypeSystem>(
    mut parser: Parser,
) -> Result<(Parser, CanonicalTerm<TypeSystem>), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    parser.expect(&Token::OpenParen)?;
    let (mut parser, term) = parse_term_root(parser.clone())?;
    parser.expect(&Token::CloseParen)?;
    return Ok((parser, term));
}

fn parse_atom<TypeSystem>(parser: Parser) -> Result<(Parser, CanonicalTerm<TypeSystem>), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    let mut errors = Vec::new();

    match parse_modifier(parser.clone()) {
        Ok((parser, parsed_modifier)) => {
            let term = Modifier::from_parsed(parsed_modifier.clone())
                .ok_or(ParseError::BadModifier)?
                .apply();
            return Ok((parser, term));
        }
        Err(e) => errors.push(e),
    }

    match parse_parenthesised_term(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    match TypeSystem::Constant::parse(parser.clone()) {
        Ok((parser, c)) => return Ok((parser, CanonicalTerm::Constant(c))),
        Err(e) => errors.push(e),
    }

    match parse_variable(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    Err(ParseError::Any(errors))
}

fn parse_term_root<TypeSystem>(
    parser: Parser,
) -> Result<(Parser, CanonicalTerm<TypeSystem>), ParseError>
where
    TypeSystem: IsTypeSystem,
{
    let mut errors = Vec::new();

    match parse_abstraction(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    match parse_application(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    Err(ParseError::Any(errors))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedModifier<TypeSystem>
where
    TypeSystem: IsTypeSystem,
{
    name: Name,
    args: Vec<CanonicalTerm<TypeSystem>>,
}

#[derive(Clone, Debug)]
enum Modifier<TypeSystem>
where
    TypeSystem: IsTypeSystem,
{
    Subst(Name, CanonicalTerm<TypeSystem>, CanonicalTerm<TypeSystem>),
    BetaReduce(CanonicalTerm<TypeSystem>),
    NormalOrderReduce(CanonicalTerm<TypeSystem>),
    ChurchNumeral(num_bigint::BigUint),
}

impl<TypeSystem> Modifier<TypeSystem>
where
    TypeSystem: IsTypeSystem,
{
    fn from_parsed(parsed: ParsedModifier<TypeSystem>) -> Option<Modifier<TypeSystem>> {
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

    fn apply(self) -> CanonicalTerm<TypeSystem> {
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

pub trait Parse: Sized {
    fn parse(parser: Parser) -> Result<(Parser, Self), ParseError>;
}
