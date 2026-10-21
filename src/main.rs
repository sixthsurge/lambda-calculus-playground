#![allow(non_snake_case)]

use anyhow::Context;
use color_print::cprintln;
use is_variant::IsVariant;
use itertools::Itertools;
use num_bigint::BigUint;
use rustc_hash::{FxHashMap, FxHashSet};
use rustyline::{DefaultEditor, error::ReadlineError};
use std::{
    io::{Write, stdin},
    iter::Peekable,
    str::Chars,
    sync::Arc,
};
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

#[derive(Clone, Debug, PartialEq, Eq, IsVariant)]
enum Term {
    Variable(Name),
    Abstraction(Name, Box<Term>),
    Application(Box<Term>, Box<Term>),
}

impl Term {
    fn cnum(value: BigUint) -> Self {
        let f: Name = "f".into();
        let x: Name = "x".into();
        let mut term = Term::Variable(x.clone());

        let mut counter = BigUint::ZERO;
        while counter < value {
            term = Term::Application(Box::new(Term::Variable(f.clone())), Box::new(term));
            counter += BigUint::ONE;
        }

        term = Term::Abstraction(x, Box::new(term));
        term = Term::Abstraction(f, Box::new(term));

        term
    }

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

    // Wrap self in (\name.self term)
    fn with_symbol(&self, name: Name, definition: Self) -> Self {
        Self::Application(
            Box::new(Self::Abstraction(name, Box::new(self.clone()))),
            Box::new(definition),
        )
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

    fn is_beta_redex(&self) -> bool {
        match self {
            Self::Application(f, _) if f.is_abstraction() => true,
            _ => false,
        }
    }

    fn beta_reduce(&mut self) -> bool {
        match self {
            Self::Abstraction(_, M) => M.beta_reduce(),
            Self::Application(f, N) => {
                if let Self::Abstraction(x, M) = f.as_ref() {
                    *self = M.substitute(x, N);
                    true
                } else {
                    f.beta_reduce() || N.beta_reduce()
                }
            }
            _ => false,
        }
    }

    fn value_from_cnum(&self) -> Option<BigUint> {
        let Term::Abstraction(f, rest) = self else {
            return None;
        };
        let Term::Abstraction(x, rest) = rest.as_ref() else {
            return None;
        };
        let mut rest = rest.as_ref();

        // repeated applications of f.
        let mut f_application_count = BigUint::ZERO;
        while let Term::Application(f_dash, new_rest) = rest {
            let Term::Variable(f_dash_name) = f_dash.as_ref() else {
                return None;
            };
            if f_dash_name != f {
                return None;
            }
            f_application_count += BigUint::ONE;
            rest = new_rest;
        }

        // finally we should have a variable.
        if let Term::Variable(name) = rest
            && name == x
        {
            Some(f_application_count)
        } else {
            None
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

        // Char tokens
        for (c, token) in [
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
struct Parser<'tokens, 'playground> {
    tokens: &'tokens [Token],
    playground: &'playground LambdaPlayground,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
enum ParseErr {
    #[error("unexpected eof")]
    UnexpectedEof,
    #[error("expected {0:?}")]
    ExpectedSpecificToken(Token),
    #[error("any of: {0:?}")]
    Any(Vec<ParseErr>),
    #[error("bad modifier: {0:?}")]
    BadModifier(ParsedModifier),
}

impl<'tokens, 'playground> Parser<'tokens, 'playground> {
    fn new(tokens: &'tokens [Token], playground: &'playground LambdaPlayground) -> Self {
        Self { tokens, playground }
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

    fn parse_variable(mut parser: Self) -> Result<(Self, Term), ParseErr> {
        match parser.peek().cloned() {
            Ok(Token::Name(name)) => {
                parser.next()?;
                Ok((parser.clone(), Term::Variable(name.clone())))
            }
            _ => Err(ParseErr::ExpectedSpecificToken(Token::Name(Name::from("")))),
        }
    }

    fn parse_abstraction(mut parser: Self) -> Result<(Self, Term), ParseErr> {
        // We support the shorthand \x y z. insteaad of \x.\y.\z.

        // Lambda.
        parser.expect(&Token::Lambda)?;

        // Argument.
        let mut args = vec![match parser.peek().cloned() {
            Ok(Token::Name(name)) => {
                parser.next()?;
                Ok(name.clone())
            }
            _ => Err(ParseErr::ExpectedSpecificToken(Token::Name(Name::from("")))),
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

        let (parser, body) = Self::parse_term(parser.clone())?;

        let mut term = body;
        for arg in args.into_iter().rev() {
            term = Term::Abstraction(arg, Box::new(term));
        }

        Ok((parser, term))
    }

    fn parse_application(parser: Self) -> Result<(Self, Term), ParseErr> {
        // Applications are left associative by convention.
        // As the parser is LL, handling applications by recursion
        // leads to infinite left recursion. So we find all atoms
        // using a loop and then construct the left associative parse tree.
        let (mut parser, mut term) = Self::parse_atom(parser)?;
        while ![Ok(Token::CloseParen), Err(ParseErr::UnexpectedEof)]
            .into_iter()
            .contains(&parser.peek().cloned())
        {
            let (new_parser, new_term) = Self::parse_atom(parser.clone())?;
            parser = new_parser;
            term = Term::Application(Box::new(term), Box::new(new_term));
        }

        Ok((parser, term))
    }

    fn parse_modifier(mut parser: Self) -> Result<(Self, ParsedModifier), ParseErr> {
        let name = match parser.peek().cloned() {
            Ok(Token::Name(name)) => {
                parser.next()?;
                Ok(name.clone())
            }
            _ => Err(ParseErr::ExpectedSpecificToken(Token::Name(Name::from("")))),
        }?;

        parser.expect(&Token::Bang)?;

        parser.expect(&Token::OpenParen)?;

        let mut args = vec![];
        while !parser.accept(&Token::CloseParen) {
            let (new_parser, term) = Self::parse_term(parser)?;
            args.push(term);
            parser = new_parser;
        }

        Ok((parser, ParsedModifier { name, args }))
    }

    fn parse_parenthesised_term(mut parser: Self) -> Result<(Self, Term), ParseErr> {
        parser.expect(&Token::OpenParen)?;
        let (mut parser, term) = Self::parse_term(parser.clone())?;
        parser.expect(&Token::CloseParen)?;
        return Ok((parser, term));
    }

    fn parse_atom(parser: Self) -> Result<(Self, Term), ParseErr> {
        let mut errors = Vec::new();

        match Self::parse_modifier(parser.clone()) {
            Ok((parser, parsed_modifier)) => {
                let term = Modifier::from_parsed(parsed_modifier.clone())
                    .ok_or(ParseErr::BadModifier(parsed_modifier))?
                    .apply(&parser.playground);
                return Ok((parser, term));
            }
            Err(e) => errors.push(e),
        }

        match Self::parse_parenthesised_term(parser.clone()) {
            Ok(result) => return Ok(result),
            Err(e) => errors.push(e),
        }

        match Self::parse_variable(parser.clone()) {
            Ok(result) => return Ok(result),
            Err(e) => errors.push(e),
        }

        Err(ParseErr::Any(errors))
    }

    fn parse_abstractive_term(parser: Self) -> Result<(Self, Term), ParseErr> {
        let mut errors = Vec::new();

        match Self::parse_abstraction(parser.clone()) {
            Ok(result) => return Ok(result),
            Err(e) => errors.push(e),
        }

        match Self::parse_application(parser.clone()) {
            Ok(result) => return Ok(result),
            Err(e) => errors.push(e),
        }

        Err(ParseErr::Any(errors))
    }

    fn parse_term(parser: Self) -> Result<(Self, Term), ParseErr> {
        let mut errors = Vec::new();

        match Self::parse_abstractive_term(parser.clone()) {
            Ok(result) => return Ok(result),
            Err(e) => errors.push(e),
        }

        Err(ParseErr::Any(errors))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedModifier {
    name: Name,
    args: Vec<Term>,
}
#[derive(clap::Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(long, default_value_t = false)]
    print_intermediate: bool,
}

#[derive(Clone, Debug)]
enum Modifier {
    Subst(Name, Term, Term),
    BetaReduce(Term),
    NormalOrderReduce(Term, bool),
    WithDict(Term),
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
                let Term::Variable(name) = it.next().unwrap() else {
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
                        false,
                    ))
                }
            }
            "wdict" => {
                if parsed.args.len() != 1 {
                    None
                } else {
                    Some(Self::WithDict(parsed.args.into_iter().next().unwrap()))
                }
            }
            "cnum" => {
                if parsed.args.len() != 1 {
                    None
                } else {
                    let Term::Variable(name) = parsed.args.into_iter().next()? else {
                        return None;
                    };
                    Some(Self::ChurchNumeral(name.as_str().parse().ok()?))
                }
            }
            _ => None,
        }
    }

    fn apply(self, playground: &LambdaPlayground) -> Term {
        match self {
            Self::Subst(name, substituted, term) => term.substitute(&name, &substituted),
            Self::BetaReduce(mut term) => {
                term.beta_reduce();
                term
            }
            Self::NormalOrderReduce(mut term, print_intermediate) => loop {
                if print_intermediate {
                    println!("{}", term);
                }
                if !term.beta_reduce() {
                    break term;
                }
            },
            Self::WithDict(mut term) => {
                for (name, definition) in playground.dictionary.iter().rev() {
                    term = term.with_symbol(name.clone().into(), definition.clone());
                }
                term
            }
            Self::ChurchNumeral(value) => Term::cnum(value),
        }
    }
}

#[derive(Debug)]
struct LambdaPlayground {
    args: Args,
    dictionary: Vec<(String, Term)>,
    terminate: bool,
}

impl LambdaPlayground {
    fn new(args: Args) -> Self {
        Self {
            args,
            dictionary: vec![],
            terminate: false,
        }
    }

    fn run_repl(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        const HISTORY_PATH: &'static str = ".lambda-history";

        let mut rl = DefaultEditor::new()?;
        rl.load_history(HISTORY_PATH).ok();

        while !self.terminate {
            let line = match rl.readline("λ: ") {
                Ok(line) => {
                    rl.add_history_entry(line.as_str())?;
                    line
                }
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    break;
                }
                Err(ReadlineError::Eof) => {
                    println!("^D");
                    break;
                }
                Err(err) => {
                    println!("<red>error</>: {:?}", err);
                    break;
                }
            };

            if let Err(e) = self.process_line(&line, true) {
                cprintln!("<red>error</>: {e:#}");
            }
        }

        rl.save_history(HISTORY_PATH)?;

        Ok(())
    }

    fn process_line(&mut self, mut remaining: &str, interactive: bool) -> anyhow::Result<()> {
        // The line has the form:
        // (identifier :=) term
        // OR
        // ! command

        if remaining.starts_with("!") {
            // Repl command.
            remaining = &remaining[1..];

            // FIXME will break paths with spaces; in future should support "" and \ escapes.
            let words = remaining.split_whitespace().collect_vec();

            if words.get(0) == Some("q").as_ref() {
                self.terminate = true;
            } else if words.get(0) == Some("load").as_ref() {
                let Some(path) = words.get(1) else {
                    return Err(CommandError::UnexpectedArgumentCount {
                        cmd: "load".into(),
                        expected: 1,
                        got: words.len() as u64 - 1,
                    }
                    .into());
                };
                let text = std::fs::read_to_string(path).map_err(|e| CommandError::FileError(e))?;
                self.process_string(&text)?;
            } else if words.len() > 0 {
                return Err(CommandError::UnknownCommand(words[0].into()).into());
            }
            return Ok(());
        }

        let mut identifier = None;
        if let Some((before, after)) = remaining.split_once(":=") {
            identifier = Some(before.trim());
            remaining = after.trim();
        }

        let tokens = Lexer::new(remaining).collect_vec();
        if tokens.is_empty() {
            return Ok(());
        }
        let term = Parser::parse_term(Parser::new(&tokens, self))?.1;
        log::trace!("Parsed {term:?}");

        if interactive {
            // Print expanded and reduced term
            let expanded = Modifier::WithDict(term.clone()).apply(self);
            let reduced =
                Modifier::NormalOrderReduce(expanded, self.args.print_intermediate).apply(self);
            println!("{}", reduced);

            if let Some(val) = reduced.value_from_cnum() {
                cprintln!("<cyan>note</>: This is the Church numeral for <yellow>{val}</>.");
            }
        }

        if let Some(ident) = identifier {
            self.dictionary.push((ident.trim().to_string(), term));
        }

        Ok(())
    }

    fn process_string(&mut self, string: &str) -> anyhow::Result<()> {
        for (index, line) in string.lines().enumerate() {
            if self.terminate {
                break;
            }
            if line.trim().is_empty() {
                continue;
            }
            self.process_line(line, false)
                .with_context(|| format!("on line {}", index + 1))?;
        }
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
enum CommandError {
    #[error("unknown command: {0}")]
    UnknownCommand(String),
    #[error("for command {cmd}: expected {expected} arguments, got {got}")]
    UnexpectedArgumentCount {
        cmd: String,
        expected: u64,
        got: u64,
    },
    #[error("io error: {0}")]
    FileError(std::io::Error),
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let args = <Args as clap::Parser>::parse();

    LambdaPlayground::new(args).run_repl()?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::Term;

    #[test]
    fn test_cnum_conversion() {
        // Church numeral <-> int.
        for x in [0 as u32, 1, 42].into_iter() {
            assert_eq!(Some(x.into()), Term::cnum(x.into()).value_from_cnum());
        }
    }
}
