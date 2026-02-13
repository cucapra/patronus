// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use patronus::expr::*;
use patronus::smt::{SmtCommand, read_command, serialize_cmd};
use rustc_hash::FxHashMap;
use std::io::{BufReader, BufWriter};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(name = "simplify")]
#[command(author = "Kevin Laeufer <laeufer@cornell.edu>")]
#[command(version)]
#[command(about = "Parses a SMT file, simplifies it and writes the simplified version to an output file.", long_about = None)]
struct Args {
    #[arg(long)]
    do_not_simplify: bool,
    #[arg(value_name = "INPUT", index = 1)]
    input_file: PathBuf,
    #[arg(value_name = "OUTPUT", index = 2)]
    output_file: PathBuf,
}

fn main() {
    let args = Args::parse();

    // open input file
    let in_file = std::fs::File::open(args.input_file).expect("failed to open input file");
    let mut in_reader = BufReader::new(in_file);

    // open output file
    let out_file =
        std::fs::File::create(args.output_file).expect("failed to open output file for writing");
    let mut out = BufWriter::new(out_file);

    // read and write commands
    let mut ctx = Context::default();
    let mut st = FxHashMap::default();
    let mut simplifier = Simplifier::new(SparseExprMap::default());
    while let Some(cmd) =
        read_command(&mut in_reader, &mut ctx, &mut st).expect("failed to read command")
    {
        let cmd = if args.do_not_simplify {
            cmd
        } else {
            simplify(&mut ctx, &mut simplifier, cmd)
        };
        serialize_cmd(&mut out, Some(&ctx), &cmd).expect("failed to write command");
    }
}

fn simplify<T: ExprMap<Option<ExprRef>>>(
    ctx: &mut Context,
    s: &mut Simplifier<T>,
    cmd: SmtCommand,
) -> SmtCommand {
    match cmd {
        SmtCommand::Assert(e) => SmtCommand::Assert(s.simplify(ctx, e)),
        SmtCommand::DefineConst(sym, value) => SmtCommand::DefineConst(sym, s.simplify(ctx, value)),
        SmtCommand::CheckSatAssuming(e) => {
            SmtCommand::CheckSatAssuming(e.into_iter().map(|e| s.simplify(ctx, e)).collect())
        }
        other => other,
    }
}
