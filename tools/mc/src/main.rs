// Copyright 2023 The Regents of the University of California
// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::error::ErrorKind;
use clap::{CommandFactory, Parser, ValueEnum};
use patronus::expr::*;
use patronus::mc::{PdrOption, bmc, pdr};
use patronus::smt::*;
use patronus::system::transform::simplify_expressions;
use patronus::*;
use std::fs::File;

#[derive(Parser, Debug)]
#[command(name = "mc")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Performs model checking on a btor2 file.", long_about = None)]
struct Args {
    #[arg(
        long,
        value_enum,
        default_value = "bitwuzla",
        help = "the SMT solver to use"
    )]
    solver: SolverChoice,
    #[arg(short, long, default_value = "bmc", help = "model checking engine")]
    engine: ModelCheckEngine,
    #[arg(short, long, help = "max BMC depth (bmc engine only) [default: 25]")]
    kmax: Option<u64>,
    #[arg(short, long)]
    verbose: bool,
    #[arg(short, long)]
    skip_simplify: bool,
    #[arg(short, long)]
    dump_smt: bool,
    #[arg(long, help = "disable UNSAT core generalization (for PDR engine only)")]
    disable_unsat_cores: bool,
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum ModelCheckEngine {
    Bmc,
    Pdr,
}

fn main() {
    let args = Args::parse();

    if args.kmax.is_some() && args.engine != ModelCheckEngine::Bmc {
        Args::command()
            .error(
                ErrorKind::ArgumentConflict,
                "--kmax can only be used with the bmc engine (--engine bmc)",
            )
            .exit();
    }
    let kmax = args.kmax.unwrap_or(25);

    if args.disable_unsat_cores && args.engine != ModelCheckEngine::Pdr {
        Args::command()
            .error(
                ErrorKind::ArgumentConflict,
                "--disable-unsat-cores can only be used with the pdr engine (--engine pdr)",
            )
            .exit();
    }

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
    let k_max = if sys.states.is_empty() {
        if args.verbose {
            println!(
                "System {} has no states. Reducing BMC to a single cycle.",
                sys.name
            );
        }
        0
    } else {
        kmax
    };
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
    let res = match args.engine {
        ModelCheckEngine::Bmc => bmc(
            &mut ctx,
            &mut smt_ctx,
            &sys,
            check_constraints,
            check_bad_states_individually,
            k_max,
        ),
        ModelCheckEngine::Pdr => {
            let mut opts = vec![];

            // Auto-disable UNSAT core generalization for solvers that don't support
            // `(get-unsat-assumptions)` (e.g. YICES2), since the core path would otherwise
            // error out.
            if args.disable_unsat_cores || !solver.supports_get_unsat_assumptions() {
                if args.verbose && !args.disable_unsat_cores {
                    println!(
                        "{} does not support (get-unsat-assumptions); disabling UNSAT core generalization.",
                        solver.name()
                    );
                }
                opts.push(PdrOption::DisableUnsatCores);
            }

            pdr(&mut ctx, &mut smt_ctx, &sys, opts)
        }
    }
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
