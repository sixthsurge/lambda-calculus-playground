#![allow(non_snake_case)]

mod reduction;
mod term_parsing;
mod term_representation;
mod tromp_diagram;
mod type_system;

use std::{fmt::Display, str::FromStr};

use anyhow::Context;
use color_print::cprintln;
use enum_assoc::Assoc;
use itertools::Itertools;
use rustyline::{error::ReadlineError, DefaultEditor};
use thiserror::Error;

use crate::{
    reduction::{normal_order_reduction, normal_order_reduction_iter},
    term_parsing::{parse_term, ParseError},
    term_representation::{CanonicalTerm, Name, TermRepresentation},
    type_system::{IsTypeSystem, SimplyTypedLambdaCalculus, TypingContext, UntypedLambdaCalculus},
};

#[derive(Clone, Copy, Debug, Assoc, PartialEq, Eq)]
#[func(
    fn name(&self) -> &'static str,
    fn from_name(name: &str) -> Option<Self>,
)]
enum Mode {
    #[assoc(name = "untyped")]
    Untyped,
    #[assoc(name = "stlc")]
    SimplyTyped,
}

#[derive(Clone, Debug, Error)]
#[error("unknown mode")]
struct ModeErr;

impl FromStr for Mode {
    type Err = ModeErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_name(s).ok_or(ModeErr)
    }
}

impl Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

#[derive(clap::Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(long, default_value_t = Mode::Untyped)]
    mode: Mode,
    #[arg(long, default_value_t = false)]
    print_intermediate: bool,
    #[arg(long, default_value_t = -1)]
    stop_after: i64,
}

#[derive(Debug)]
struct LambdaPlayground<TypeSystem>
where
    TypeSystem: IsTypeSystem,
{
    mode: Mode,
    dictionary: Vec<(String, CanonicalTerm<TypeSystem>)>,
    terminate: bool,
    print_intermediate: bool,
    stop_after: i64,
}

impl<TypeSystem> LambdaPlayground<TypeSystem>
where
    TypeSystem: IsTypeSystem,
{
    fn new(mode: Mode, print_intermediate: bool, stop_after: i64) -> Self {
        Self {
            mode,
            dictionary: vec![],
            terminate: false,
            print_intermediate,
            stop_after,
        }
    }

    fn run_repl(&mut self) -> anyhow::Result<()> {
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
        // (identifier =) term
        // OR
        // ! command

        if remaining.starts_with("!") {
            // Repl command.
            remaining = &remaining[1..];

            // FIXME will break paths with spaces; in future should support "" and \ escapes.
            let words = remaining.split_whitespace().collect_vec();

            match words.get(0).copied() {
                Some("q") => {
                    self.terminate = true;
                }
                Some("help") => {
                    println!("available commands:");
                    println!("  !help        | display this message");
                    println!("  !q           | exit the REPL");
                    println!("  !load <path> | source definitions from a file");
                    println!("  !dict        | print all definitions");
                    println!("  !req <mode>  | require a specific mode (untyped, stlc, etc)");
                }
                Some("load") => {
                    let Some(path) = words.get(1) else {
                        return Err(CommandError::UnexpectedArgumentCount {
                            cmd: "load".into(),
                            expected: 1,
                            got: words.len() as u64 - 1,
                        }
                        .into());
                    };
                    let text =
                        std::fs::read_to_string(path).map_err(|e| CommandError::FileError(e))?;
                    self.process_string(&text)?;
                }
                Some("dict") => {
                    for (name, definition) in &self.dictionary {
                        println!("{} = {}", name, definition);
                    }
                }
                Some("req") => {
                    let mode: Mode = words
                        .get(1)
                        .copied()
                        .ok_or_else(|| anyhow::anyhow!("expected argument after 'req'"))?
                        .parse()?;
                    if mode != self.mode {
                        self.terminate = true;
                        return Err(anyhow::anyhow!(
                            "required mode '{}' does not match current mode '{}'",
                            mode,
                            self.mode
                        ));
                    }
                }
                Some(a) => {
                    return Err(CommandError::UnknownCommand(a.into()).into());
                }
                None => {
                    return Err(CommandError::ExpectedCommand.into());
                }
            }

            return Ok(());
        }

        let mut identifier = None;
        if let Some((before, after)) = remaining.split_once("=") {
            identifier = Some(before.trim());
            remaining = after.trim();
        }

        let term = match parse_term(remaining) {
            Ok(t) => t,
            Err(ParseError::NoTokens) => {
                // Allow empty lines.
                return Ok(());
            }
            Err(e) => return Err(e.into()),
        };
        log::trace!("Parsed {term:?}");

        if interactive {
            // Print expanded and reduced term
            let mut expanded = term.clone();
            for (name, definition) in self.dictionary.iter().rev() {
                expanded.substitute(&Name::from(name.as_str()), definition);
            }

            /*
            let mut de_bruijn = DeBruijnIndexedTerm::from_canonical(&expanded, -1, &mut vec![]);
            println!("De Bruijn term: {de_bruijn}");
            loop {
                if !de_bruijn.beta_reduce() {
                    println!("  => {de_bruijn}");
                    break;
                }
            }
            */

            match TypeSystem::typecheck(&expanded, &TypingContext::<TypeSystem>::new()) {
                Ok(ty) => cprintln!("Type: <yellow>{ty}</>"),
                Err(e) => {
                    cprintln!("<red>Type error</>: {e}");
                    anyhow::bail!("type error");
                }
            }

            let mut reduced = expanded.clone();
            for iter in 0.. {
                if iter >= self.stop_after && self.stop_after > 0 {
                    break;
                }
                if self.print_intermediate {
                    println!("=> {reduced}");
                }
                if !normal_order_reduction_iter(&mut reduced) {
                    break;
                }
            }
            if !self.print_intermediate {
                println!("=> {reduced}");
            }

            if let Some(val) = reduced.church_numeral_value() {
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

    fn process(&self, mut term: CanonicalTerm<TypeSystem>) -> CanonicalTerm<TypeSystem> {
        for (name, definition) in self.dictionary.iter().rev() {
            term.substitute(&Name::from(name.as_str()), definition);
        }
        normal_order_reduction(&mut term);
        term
    }
}

#[derive(Debug, thiserror::Error)]
enum CommandError {
    #[error("expected command")]
    ExpectedCommand,
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

fn main() -> anyhow::Result<()> {
    env_logger::init();

    let args = <Args as clap::Parser>::parse();

    match args.mode {
        Mode::Untyped => {
            LambdaPlayground::<UntypedLambdaCalculus>::new(
                args.mode,
                args.print_intermediate,
                args.stop_after,
            )
            .run_repl()?;
        }
        Mode::SimplyTyped => {
            LambdaPlayground::<SimplyTypedLambdaCalculus>::new(
                args.mode,
                args.print_intermediate,
                args.stop_after,
            )
            .run_repl()?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;

    #[test]
    fn church_numeral_arithmetic() {
        let mut playground =
            LambdaPlayground::<UntypedLambdaCalculus>::new(Mode::Untyped, false, -1);

        playground
            .process_string(
                r#"
                succ = \n f x. f (n f x)
                pred = \n f x. n (\g. \h. h (g f)) (\u. x) (\u. u)
                add = \m n f x. m f (n f x)
                sub = \m n. n pred m
                mul = \m n. m (add n) cnum!(0)
                pow = \base power. power base
                iszero = \n. n (\x. F) T
                leq = \m n. iszero (sub m n)
                eq = \m n. and (leq m n) (leq n m)
                "#,
            )
            .unwrap();

        assert_eq!(
            playground
                .process("succ cnum!(4)".parse().unwrap())
                .church_numeral_value(),
            Some(BigUint::from(5u32))
        );
        assert_eq!(
            playground
                .process("pred cnum!(4)".parse().unwrap())
                .church_numeral_value(),
            Some(BigUint::from(3u32))
        );
        assert_eq!(
            playground
                .process("mul cnum!(3) cnum!(4)".parse().unwrap())
                .church_numeral_value(),
            Some(BigUint::from(12u32))
        );
        assert_eq!(
            playground
                .process("add cnum!(3) cnum!(4)".parse().unwrap())
                .church_numeral_value(),
            Some(BigUint::from(7u32))
        );
        assert_eq!(
            playground
                .process("sub cnum!(3) cnum!(4)".parse().unwrap())
                .church_numeral_value(),
            Some(BigUint::from(0u32))
        );
        assert_eq!(
            playground
                .process("sub cnum!(4) cnum!(3)".parse().unwrap())
                .church_numeral_value(),
            Some(BigUint::from(1u32))
        );
        assert_eq!(
            playground
                .process("mul cnum!(3) cnum!(4)".parse().unwrap())
                .church_numeral_value(),
            Some(BigUint::from(12u32))
        );
    }

    #[test]
    fn stlc_factorial() {
        let mut playground =
            LambdaPlayground::<SimplyTypedLambdaCalculus>::new(Mode::SimplyTyped, false, 1024);

        playground
            .process_string(
                r#"
                fac = fix (\s: (Int -> Int) n: Int. if n (mul n (s (sub n 1))) 1)
                "#,
            )
            .unwrap();
        assert_eq!(
            playground.process("fac 1".parse().unwrap()),
            "1".parse().unwrap()
        );
        assert_eq!(
            playground.process("fac 2".parse().unwrap()),
            "2".parse().unwrap()
        );
        assert_eq!(
            playground.process("fac 3".parse().unwrap()),
            "6".parse().unwrap()
        );
        assert_eq!(
            playground.process("fac 4".parse().unwrap()),
            "24".parse().unwrap()
        );
        assert_eq!(
            playground.process("fac (fac 4)".parse().unwrap()),
            "620448401733239439360000".parse().unwrap()
        );
    }
}
