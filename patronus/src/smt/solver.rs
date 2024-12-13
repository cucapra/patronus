// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprRef};
use crate::smt::serialize::serialize_cmd;
use std::io::{BufRead, BufReader, BufWriter};
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use thiserror::Error;

/// A SMT Solver Error.
#[derive(Error, Debug)]
pub enum Error {
    #[error("[smt] I/O operation failed")]
    Io(#[from] std::io::Error),
    #[error("[smt] cannot pop because the stack is already empty")]
    StackUnderflow,
    #[error("[smt] {0} reported an error:\n{1}")]
    FromSolver(String, String),
    #[error("[smt]{0} is unreachable, the process might have died")]
    SolverDead(String),
    #[error("[smt] {0} returned an unexpected response:\n{1}")]
    UnexpectedResponse(String, String),
}

pub type Result<T> = std::result::Result<T, Error>;

/// An SMT Logic.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Logic {
    All,
    QfAufbv,
    QfAbv,
}

impl Logic {
    pub(crate) fn to_smt_str(&self) -> &'static str {
        match self {
            Logic::All => "ALL",
            Logic::QfAufbv => "QF_AUFBV",
            Logic::QfAbv => "QF_ABV",
        }
    }
}

/// A command to an SMT solver.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum SmtCommand {
    Exit,
    CheckSat,
    SetLogic(Logic),
    SetOption(String, String),
    Assert(ExprRef),
    DeclareConst(ExprRef),
    DefineConst(ExprRef, ExprRef),
    CheckSatAssuming(Vec<ExprRef>),
    Push(u64),
    Pop(u64),
}

/// The result of a `(check-sat)` command.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum CheckSatResponse {
    Sat,
    Unsat,
    Unknown,
}

/// Represents a kind of SMT solver and allows that solver to be started.
pub trait Solver {
    /// Launch a new instance of this solver.
    fn start<R: Write + Send>(&self, replay_file: Option<R>) -> Result<impl SolverContext>;
    // properties
    fn name(&self) -> &str;
    fn supports_check_assuming(&self) -> bool;
    fn supports_uf(&self) -> bool;
}

/// Interface to a running SMT Solver with everything executing as blocking I/O.
pub trait SolverContext {
    fn set_logic(&mut self, option: Logic) -> Result<()>;
    fn assert(&mut self, ctx: &Context, e: ExprRef) -> Result<()>;
    fn declare_const(&mut self, ctx: &Context, symbol: ExprRef) -> Result<()>;
    fn define_const(&mut self, ctx: &Context, symbol: ExprRef, expr: ExprRef) -> Result<()>;
    fn check_sat_assuming(
        &mut self,
        ctx: &Context,
        props: impl IntoIterator<Item = ExprRef>,
    ) -> Result<CheckSatResponse>;
    fn check_sat(&mut self) -> Result<CheckSatResponse>;
    fn push(&mut self) -> Result<()>;
    fn pop(&mut self) -> Result<()>;
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SmtLibSolver {
    name: &'static str,
    args: &'static [&'static str],
    options: &'static [&'static str],
    supports_uf: bool,
    supports_check_assuming: bool,
}

impl Solver for SmtLibSolver {
    fn start<R: Write + Send>(&self, replay_file: Option<R>) -> Result<impl SolverContext> {
        let mut proc = Command::new(self.name)
            .args(self.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let stdin = BufWriter::new(proc.stdin.take().unwrap());
        let stdout = BufReader::new(proc.stdout.take().unwrap());
        let stderr = proc.stderr.take().unwrap();
        let mut solver = SmtLibSolverCtx {
            name: self.name.to_string(),
            proc,
            stdin,
            stdout,
            stderr,
            stack_depth: 0,
            response: String::new(),
            replay_file,
            has_error: false,
        };
        for option in self.options.iter() {
            solver.write_cmd(
                None,
                &SmtCommand::SetOption(option.to_string(), "true".to_string()),
            )?
        }
        Ok(solver)
    }

    fn name(&self) -> &str {
        self.name
    }

    fn supports_check_assuming(&self) -> bool {
        self.supports_check_assuming
    }

    fn supports_uf(&self) -> bool {
        self.supports_uf
    }
}

/// Launches an SMT solver and communicates through `stdin` using SMTLib commands.
pub struct SmtLibSolverCtx<R: Write + Send> {
    name: String,
    proc: std::process::Child,
    stdin: BufWriter<std::process::ChildStdin>,
    stdout: BufReader<std::process::ChildStdout>,
    stderr: std::process::ChildStderr,
    stack_depth: usize,
    response: String,
    replay_file: Option<R>,
    /// keeps track of whether there was an error from the solver which might make regular shutdown
    /// impossible
    has_error: bool,
}

impl<R: Write + Send> SmtLibSolverCtx<R> {
    #[inline]
    fn write_cmd(&mut self, ctx: Option<&Context>, cmd: &SmtCommand) -> Result<()> {
        if let Some(rf) = self.replay_file.as_mut() {
            serialize_cmd(rf, ctx, cmd)?;
        }
        serialize_cmd(&mut self.stdin, ctx, cmd)?;
        if let Some(rf) = self.replay_file.as_mut() {
            rf.flush()?;
        }
        match self.stdin.flush() {
            Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => {
                // make sure we drop the replay file
                self.replay_file.take();
                Err(Error::SolverDead(self.name.clone()))
            }
            Err(other) => Err(other.into()),
            Ok(_) => Ok(()),
        }
    }

    /// after this function executes, the result will be available in `self.result`.
    fn read_response(&mut self) -> Result<()> {
        self.stdin.flush()?; // make sure that the commands reached the solver
        self.response.clear();
        // our basic assumptions are:
        // 1. the solver will terminate its answer with '\n'
        // 2. the answer will contain a balanced number of parenthesis
        self.stdout.read_line(&mut self.response)?;
        while count_parens(&self.response) > 0 {
            self.response.push(' ');
            self.stdout.read_line(&mut self.response)?;
        }

        // check to see if there was an error reported on stdout
        if self.response.trim_start().starts_with("(error") {
            let trimmed = self.response.trim();
            let start = "(error ".len();
            let msg = &trimmed[start..(trimmed.len() - start - 1)];
            self.has_error = true;
            Err(Error::FromSolver(self.name.clone(), msg.to_string()))
        } else {
            // check if the process is still alive
            match self.proc.try_wait() {
                Ok(Some(status)) if !status.success() => {
                    // solver terminated with error return code
                    // check for output on stderror
                    let mut err = vec![];
                    self.stderr.read_to_end(&mut err)?;
                    self.has_error = true;
                    Err(Error::FromSolver(
                        self.name.clone(),
                        String::from_utf8_lossy(&err).to_string(),
                    ))
                }
                _ => Ok(()),
            }
        }
    }

    fn read_sat_response(&mut self) -> Result<CheckSatResponse> {
        self.read_response()?;
        let response = self.response.trim();
        match response {
            "sat" => Ok(CheckSatResponse::Sat),
            "unsat" => Ok(CheckSatResponse::Unsat),
            other => Err(Error::UnexpectedResponse(
                self.name.clone(),
                other.to_string(),
            )),
        }
    }
}

fn count_parens(s: &str) -> i64 {
    s.chars().fold(0, |count, cc| match cc {
        '(' => count + 1,
        ')' => count - 1,
        _ => count,
    })
}

impl<R: Write + Send> Drop for SmtLibSolverCtx<R> {
    fn drop(&mut self) {
        // try to close the child process as not to leak resources
        if self.write_cmd(None, &SmtCommand::Exit).is_err() {
            if self.has_error {
                return;
            } else {
                panic!("failed to send exit command");
            }
        }
        let status = self
            .proc
            .wait()
            .expect("failed to wait for SMT solver to exit");
        if !self.has_error {
            // if everything has gone smoothly so far, we expect a successful exit
            assert!(
                status.success(),
                "There was an error with the solver exiting: {:?}",
                status
            );
        }
    }
}

impl<R: Write + Send> SolverContext for SmtLibSolverCtx<R> {
    fn set_logic(&mut self, logic: Logic) -> Result<()> {
        self.write_cmd(None, &SmtCommand::SetLogic(logic))
    }

    fn assert(&mut self, ctx: &Context, e: ExprRef) -> Result<()> {
        self.write_cmd(Some(ctx), &SmtCommand::Assert(e))
    }

    fn declare_const(&mut self, ctx: &Context, symbol: ExprRef) -> Result<()> {
        self.write_cmd(Some(ctx), &SmtCommand::DeclareConst(symbol))
    }

    fn define_const(&mut self, ctx: &Context, symbol: ExprRef, expr: ExprRef) -> Result<()> {
        self.write_cmd(Some(ctx), &SmtCommand::DefineConst(symbol, expr))
    }

    fn check_sat_assuming(
        &mut self,
        ctx: &Context,
        props: impl IntoIterator<Item = ExprRef>,
    ) -> Result<CheckSatResponse> {
        let props: Vec<ExprRef> = props.into_iter().collect();
        self.write_cmd(Some(ctx), &SmtCommand::CheckSatAssuming(props))?;
        self.read_sat_response()
    }

    fn check_sat(&mut self) -> Result<CheckSatResponse> {
        self.write_cmd(None, &SmtCommand::CheckSat)?;
        self.read_sat_response()
    }

    fn push(&mut self) -> Result<()> {
        self.write_cmd(None, &SmtCommand::Push(1))?;
        self.stack_depth += 1;
        Ok(())
    }

    fn pop(&mut self) -> Result<()> {
        if self.stack_depth > 0 {
            self.write_cmd(None, &SmtCommand::Pop(1))?;
            self.stack_depth -= 1;
            Ok(())
        } else {
            Err(Error::StackUnderflow)
        }
    }
}

const BITWUZLA: SmtLibSolver = SmtLibSolver {
    name: "bitwuzla",
    args: &[],
    options: &["incremental"],
    supports_uf: false,
    supports_check_assuming: true,
};

const YICES2: SmtLibSolver = SmtLibSolver {
    name: "yices-smt2",
    args: &["--incremental"],
    options: &[],
    supports_uf: false, // actually true, but ignoring for now
    supports_check_assuming: false,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitwuzla_error() {
        let mut ctx = Context::default();
        let replay = Some(std::fs::File::create("replay.smt").unwrap());
        let mut solver = BITWUZLA.start(replay).unwrap();
        let a = ctx.bv_symbol("a", 3);
        let e = ctx.build(|c| c.equal(a, c.bit_vec_val(3, 3)));
        solver.assert(&ctx, e).unwrap();
        let res = solver.check_sat();
        assert!(res.is_err(), "a was not declared!");
        // after this error, the solver is dead and won't respond!
        let res = solver.declare_const(&ctx, a);
        assert!(res.is_err());
    }

    #[test]
    fn test_bitwuzla() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("a", 3);
        let e = ctx.build(|c| c.equal(a, c.bit_vec_val(3, 3)));
        let replay = Some(std::fs::File::create("replay.smt").unwrap());
        let mut solver = BITWUZLA.start(replay).unwrap();
        solver.declare_const(&ctx, a).unwrap();
        let res = solver.check_sat_assuming(&ctx, [e]);
        assert_eq!(res.unwrap(), CheckSatResponse::Sat);
    }
}
