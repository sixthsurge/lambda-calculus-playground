#![allow(non_snake_case)]

use itertools::Itertools;
use log::trace;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{io::stdin, iter::Peekable, str::Chars, sync::Arc};
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Name {
    name: Arc<str>,
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl Name {
    fn as_str(&self) -> &str {
        self.name.as_ref()
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.name.as_ref()
    }
}

impl From<String> for Name {
    fn from(value: String) -> Self {
        Self {
            name: Arc::from(value),
        }
    }
}

impl From<&str> for Name {
    fn from(value: &str) -> Self {
        Self {
            name: Arc::from(value),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Variable(Name),
    Abstraction(Name, Box<Term>),
    Application(Box<Term>, Box<Term>),
}

impl Term {
    fn free_variables(&self) -> FxHashSet<Name> {
        match self {
            Self::Variable(name) => std::iter::once(name).cloned().collect(),
            Self::Abstraction(name, body) => {
                let mut s = body.free_variables();
                s.remove(name);
                s
            }
            Self::Application(m_1, m_2) => m_1
                .free_variables()
                .union(&m_2.free_variables())
                .cloned()
                .collect(),
        }
    }

    /// Capture-avoiding substitution.
    fn substitute(&self, x: &Name, N: &Term) -> Term {
        match self {
            Self::Variable(y) => {
                if y == x {
                    N.clone()
                } else {
                    Term::Variable(y.clone())
                }
            }
            Self::Abstraction(y, M) => {
                if y == x {
                    Term::Abstraction(x.clone(), M.clone())
                } else {
                    let fv_N = N.free_variables();
                    if !fv_N.contains(y) {
                        Term::Abstraction(y.clone(), Box::new(M.substitute(x, N)))
                    } else {
                        // Find fresh variable name.
                        let fv_M = M.free_variables();
                        let y_dash = (0..)
                            .map(|i| Name::from(format!("{}{}", y.as_str(), i)))
                            .find(|name| !fv_N.contains(name) && !fv_M.contains(name))
                            .unwrap();

                        Term::Abstraction(
                            y_dash.clone(),
                            Box::new(M.substitute(y, &Term::Variable(y_dash))),
                        )
                        .substitute(x, N)
                    }
                }
            }
            Self::Application(M_1, M_2) => Term::Application(
                Box::new(M_1.substitute(x, N)),
                Box::new(M_2.substitute(x, N)),
            ),
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Variable(name) => f.write_str(name.as_str()),
            Self::Abstraction(arg, body) => write!(f, "\\{}.{}", arg.as_str(), &body),
            Self::Application(a, b) => write!(f, "({} {})", &a, &b),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Name(Name),
    Lambda,
    Dot,
    OpenParen,
    CloseParen,
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

        // Char tokens
        for (c, token) in [
            ('\\', Token::Lambda),
            ('.', Token::Dot),
            ('(', Token::OpenParen),
            (')', Token::CloseParen),
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

        None
    }
}

#[derive(Clone, Debug)]
struct Parser<'tokens> {
    tokens: &'tokens [Token],
}

#[derive(Clone, Debug, Error)]
enum ParseErr {
    #[error("unexpected eof")]
    UnexpectedEof,
    #[error("expected {0:?}")]
    ExpectedSpecificToken(Token),
    #[error("any of: [0:?]")]
    Any(Vec<ParseErr>),
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
            Err(ParseErr::ExpectedSpecificToken(token.clone()))
        }
    }
}

fn parse_variable(mut parser: Parser) -> Result<(Parser, Term), ParseErr> {
    match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok((parser.clone(), Term::Variable(name.clone())))
        }
        _ => Err(ParseErr::ExpectedSpecificToken(Token::Name(Name::from("")))),
    }
}

fn parse_abstraction(mut parser: Parser) -> Result<(Parser, Term), ParseErr> {
    // Lambda.
    parser.expect(&Token::Lambda)?;

    // Argument.
    let arg = match parser.peek().cloned() {
        Ok(Token::Name(name)) => {
            parser.next()?;
            Ok(name.clone())
        }
        _ => Err(ParseErr::ExpectedSpecificToken(Token::Name(Name::from("")))),
    }?;

    // Dot.
    parser.expect(&Token::Dot)?;

    // Body.
    let (parser, body) = parse_term(parser.clone())?;

    Ok((parser, Term::Abstraction(arg, Box::new(body))))
}

fn parse_application(mut parser: Parser) -> Result<(Parser, Term), ParseErr> {
    parser.expect(&Token::OpenParen)?;
    let (parser, t1) = parse_term(parser)?;
    let (mut parser, t2) = parse_term(parser)?;
    parser.expect(&Token::CloseParen)?;

    Ok((parser, Term::Application(Box::new(t1), Box::new(t2))))
}

fn parse_parenthesised_term(mut parser: Parser) -> Result<(Parser, Term), ParseErr> {
    parser.expect(&Token::OpenParen)?;
    let (mut parser, term) = parse_term(parser.clone())?;
    parser.expect(&Token::CloseParen)?;
    return Ok((parser, term));
}

fn parse_term(mut parser: Parser) -> Result<(Parser, Term), ParseErr> {
    let mut errors = Vec::new();

    match parse_parenthesised_term(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }
    match parse_abstraction(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }
    match parse_application(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    match parse_variable(parser.clone()) {
        Ok(result) => return Ok(result),
        Err(e) => errors.push(e),
    }

    Err(ParseErr::Any(errors))
}

#[derive(clap::Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {}

#[derive(Clone, Debug, Default)]
struct Repl {
    terms: FxHashMap<String, Term>,
}

#[derive(Clone, Debug)]
enum Modifier {
    Subst(Name, Term),
}

impl Modifier {
    fn parse(remaining: &str) -> Option<(Modifier, &str)> {
        // TODO handle errors with grace
        if let Some(remaining) = remaining.strip_prefix("subst") {
            let (_, a) = remaining.split_once('[')?;
            let (b, remaining) = a.split_once(']')?;

            let (name, term) = b.split_once("->")?;

            Some((
                Modifier::Subst(
                    Name::from(name.trim()),
                    parse_term(Parser::new(&Lexer::new(term).collect_vec()))
                        .unwrap_or_else(|e| panic!("failed to parse term: {e}"))
                        .1,
                ),
                remaining,
            ))
        } else {
            None
        }
    }

    fn apply(&self, term: &mut Term) {
        match self {
            Self::Subst(name, substituted) => {
                *term = term.substitute(name, substituted);
            }
        }
    }
}

impl Repl {
    fn run(&mut self) {
        let stdin = stdin();
        let mut line_buf = String::new();

        while let Ok(n) = stdin.read_line(&mut line_buf) {
            let mut remaining = &line_buf[..n];

            // The line has the form:
            // (identifier :=) (modifier!) term

            let mut identifier = None;
            if let Some((before, after)) = remaining.split_once(":=") {
                identifier = Some(before.trim());
                remaining = after.trim();
            }

            let mut modifier = None;
            if let Some((parsed, after)) = Modifier::parse(remaining) {
                modifier = Some(parsed);
                remaining = after;
            }

            let mut term = parse_term(Parser::new(&Lexer::new(remaining).collect_vec()))
                    .unwrap_or_else(|e| panic!("failed to parse term: {e}"))
                    .1;

            trace!("{identifier:?} := {modifier:?} {term:?}");

            if let Some(modifier) = modifier {
                modifier.apply(&mut term);
            }

            println!("{}", term);

            if let Some(ident) = identifier {
                self.terms.insert(ident.trim().to_string(), term);
            }

            line_buf.clear();
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let args = <Args as clap::Parser>::parse();

    Repl::default().run();

    Ok(())
}
