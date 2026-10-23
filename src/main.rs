#![allow(non_snake_case)]

mod reduction;
mod term_parsing;
mod term_representation;
mod tromp_diagram;

use anyhow::Context;
use color_print::cprintln;
use itertools::Itertools;
use rustyline::{error::ReadlineError, DefaultEditor};

use crate::{
    reduction::normal_order_reduction_iter,
    term_parsing::{parse_term, ParseErr},
    term_representation::{CanonicalTerm, Name, TermRepresentation},
};

#[derive(clap::Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(long, default_value_t = false)]
    print_intermediate: bool,
}

#[derive(Debug)]
struct LambdaPlayground {
    dictionary: Vec<(String, CanonicalTerm)>,
    terminate: bool,
    print_intermediate: bool,
}

impl LambdaPlayground {
    fn new(print_intermediate: bool) -> Self {
        Self {
            dictionary: vec![],
            terminate: false,
            print_intermediate,
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
        // (identifier :=) term
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
        if let Some((before, after)) = remaining.split_once(":=") {
            identifier = Some(before.trim());
            remaining = after.trim();
        }

        let term = match parse_term(remaining) {
            Ok(t) => t,
            Err(ParseErr::NoTokens) => {
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

            let mut reduced = expanded.clone();
            loop {
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

    LambdaPlayground::new(args.print_intermediate).run_repl()?;

    Ok(())
}
