// Copyright 2023 The Regents of the University of California
// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::{Parser, ValueEnum};
use patronus::expr::*;
use patronus::mc::bmc;
use patronus::smt::*;
use patronus::system::transform::simplify_expressions;
use patronus::*;
use std::fs::File;

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
    skip_simplify: bool,
    #[arg(short, long)]
    dump_smt: bool,
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum SolverChoice {
    Bitwuzla,
    Yices2,
    Z3,
    CVC5,
}

fn main() {
    let args = Args::parse();
    let (mut ctx, mut sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
    if !args.skip_simplify {
        if args.verbose {
            println!("simplifying...")
        };
        // replace_anonymous_inputs_with_zero(&mut ctx, &mut sys);
        simplify_expressions(&mut ctx, &mut sys);
    }
    if args.verbose {
        println!("Loaded: {}", sys.name);
        println!("{}", sys.serialize_to_str(&ctx));
        println!();
        println!();
    }
    let k_max = 25;
    let check_constraints = true;
    let check_bad_states_individually = false;
    let solver = match args.solver {
        SolverChoice::Bitwuzla => BITWUZLA,
        SolverChoice::Yices2 => YICES2,
        SolverChoice::Z3 => Z3,
        SolverChoice::CVC5 => CVC5,
    };
    if args.verbose {
        println!("Checking up to {k_max} using {}.", solver.name());
    }
    let dump_file = if args.dump_smt {
        Some(File::create("replay.smt").unwrap())
    } else {
        None
    };
    let mut smt_ctx = solver.start(dump_file).expect("failed to start solver");
    let res = bmc(
        &mut ctx,
        &mut smt_ctx,
        &sys,
        check_constraints,
        check_bad_states_individually,
        k_max,
    )
    .unwrap();
    match res {
        mc::ModelCheckResult::Success => {
            println!("unsat");
        }
        mc::ModelCheckResult::Unknown => {
            println!("unknown");
        }
        mc::ModelCheckResult::Fail(wit) => {
            btor2::print_witness(&mut std::io::stdout(), &wit).unwrap();
        }
    }
}
