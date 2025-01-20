// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::{Parser, ValueEnum};
use patronus::expr::*;
use patronus::smt::*;
use patronus::*;

#[derive(Parser, Debug)]
#[command(name = "bmc")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Performs bounded model checking on a btor2 file.", long_about = None)]
struct Args {
    #[arg(
        long,
        value_enum,
        default_value = "bitwuzla",
        help = "the SMT solver to use"
    )]
    solver: SolverChoice,
    #[arg(short, long)]
    verbose: bool,
    #[arg(short, long)]
    dump_smt: bool,
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum SolverChoice {
    Bitwuzla,
    Yices2,
}

fn main() {
    let args = Args::parse();
    let (mut ctx, sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
    if args.verbose {
        println!("Loaded: {}", sys.name);
        println!("{}", sys.serialize_to_str(&ctx));
        println!();
        println!();
    }
    let k_max = 25;
    let checker_opts = mc::SmtModelCheckerOptions {
        check_constraints: true,
        check_bad_states_individually: true,
        save_smt_replay: args.dump_smt,
    };
    let solver = match args.solver {
        SolverChoice::Bitwuzla => BITWUZLA,
        SolverChoice::Yices2 => YICES2,
    };
    if args.verbose {
        println!(
            "Checking up to {k_max} using {} and the following options:\n{checker_opts:?}",
            solver.name()
        );
    }
    let checker = mc::SmtModelChecker::new(solver, checker_opts);
    let res = checker.check(&mut ctx, &sys, k_max).unwrap();
    match res {
        mc::ModelCheckResult::Success => {
            println!("unsat");
        }
        mc::ModelCheckResult::Fail(wit) => {
            btor2::print_witness(&mut std::io::stdout(), &wit).unwrap();
        }
    }
}
