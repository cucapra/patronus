// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecOps, BitVecValue, Value, WidthInt};
use clap::{Parser, ValueEnum, arg};
use patronus::expr::*;
use patronus::sim::*;
use patronus::system::*;
use patronus::*;
use rustc_hash::FxHashMap;
use std::io::BufRead;

#[derive(Parser, Debug)]
#[command(name = "sim")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Simulates a transitions system from a btor2 file.", long_about = None)]
struct Args {
    #[arg(short, long)]
    verbose: bool,
    #[arg(long, help = "print out signal values for each step")]
    trace_values: bool,
    #[arg(long, help = "prints out simulator instruction execution")]
    trace_instructions: bool,
    #[arg(long, help = "prints out interpreter instructions before execution")]
    show_programs: bool,
    #[arg(
        long,
        value_enum,
        default_value = "random",
        help = "initialization strategy"
    )]
    init: Init,
    #[arg(long, help = "Filename of a testbench.")]
    testbench: Option<String>,
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Init {
    Zero,
    Random,
}

fn main() {
    let args = Args::parse();
    let (ctx, sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
    if args.verbose {
        println!("Loaded: {}", sys.name);
        println!("{}", sys.serialize_to_str(&ctx));
        println!();
        println!();
    }

    // start execution
    let start_load = std::time::Instant::now();
    let mut sim = if args.trace_instructions {
        Interpreter::new_with_trace(&ctx, &sys)
    } else {
        Interpreter::new(&ctx, &sys)
    };

    if args.show_programs {
        println!("The interpreter no longer compiles to an internal program representation");
        //sim.print_programs();
    }

    match args.init {
        Init::Zero => {
            sim.init(InitKind::Zero);
        }
        Init::Random => {
            sim.init(InitKind::Random(123));
        }
    }
    let delta_load = std::time::Instant::now() - start_load;
    println!("Loaded the design into the interpreter in {:?}", delta_load);

    let testbench_file = match args.testbench {
        None => {
            println!("No testbench provided. Exiting...");
            return;
        }
        Some(tb) => tb,
    };

    let mut tb = std::io::BufReader::new(
        std::fs::File::open(testbench_file).expect("Failed to load testbench file"),
    );

    let name_to_ref = sys.get_name_map(&ctx);
    let (inputs, outputs) =
        read_header(&mut tb, &name_to_ref, &sys, &ctx).expect("Failed to read testbench header");
    if args.verbose {
        println!("Inputs: {inputs:?}");
        println!("Outputs: {outputs:?}");
    }

    let mut signals_to_print: Vec<(String, ExprRef)> = Vec::new();
    if args.trace_values {
        for (name, expr) in name_to_ref.iter() {
            // TODO: maybe filter
            if expr.get_type(&ctx).is_bit_vector() {
                // we do not print arrays
                signals_to_print.push((name.clone(), expr.clone()));
            }
        }
        signals_to_print.sort_by_key(|(name, _)| name.clone());
    }

    let start_exec = std::time::Instant::now();
    for (step_id, line) in tb.lines().flatten().enumerate() {
        do_step(
            step_id,
            &mut sim,
            &line,
            &inputs,
            &outputs,
            &signals_to_print,
        );
    }
    let delta_exec = std::time::Instant::now() - start_exec;
    println!("Executed {} steps in {:?}", sim.step_count(), delta_exec);
}

type IOInfo = Vec<(usize, ExprRef, String, WidthInt)>;

/// Correlates the header with the inputs and outputs of the system.
fn read_header(
    input: &mut impl BufRead,
    name_to_ref: &FxHashMap<String, ExprRef>,
    sys: &TransitionSystem,
    ctx: &Context,
) -> std::io::Result<(IOInfo, IOInfo)> {
    let mut line = String::new();
    input.read_line(&mut line)?;
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for (cell_id, cell) in line.split(",").enumerate() {
        let name = cell.trim();
        if let Some(signal_ref) = name_to_ref.get(name) {
            let width = signal_ref.get_bv_type(ctx).unwrap();
            if let Some(signal_ref) = sys.lookup_input(ctx, name) {
                inputs.push((cell_id, signal_ref, name.to_string(), width));
            } else if let Some(signal_ref) = sys.lookup_output(ctx, name) {
                outputs.push((cell_id, signal_ref, name.to_string(), width));
            }
        }
    }
    Ok((inputs, outputs))
}

/// Reads one line in the CSV, applies inputs, checks outputs and finally steps the system.
fn do_step(
    step_id: usize,
    sim: &mut impl Simulator,
    line: &str,
    inputs: &[(usize, ExprRef, String, WidthInt)],
    outputs: &[(usize, ExprRef, String, WidthInt)],
    signal_to_print: &[(String, ExprRef)],
) {
    // apply inputs
    let mut input_iter = inputs.iter();
    if let Some(mut input) = input_iter.next() {
        for (cell_id, cell) in line.split(",").enumerate() {
            if cell_id == input.0 {
                // apply input
                let trimmed = cell.trim();
                if trimmed.to_ascii_lowercase() != "x" {
                    let value = u64::from_str_radix(trimmed, 10).unwrap();
                    let width = input.3;
                    sim.set(input.1, &BitVecValue::from_u64(value, width));
                }

                // get next input
                if let Some(next_input) = input_iter.next() {
                    input = next_input;
                } else {
                    break;
                }
            }
        }
    }

    // print values if the option is enabled
    if !signal_to_print.is_empty() {
        println!();
        for (name, expr) in signal_to_print.iter() {
            if let Value::BitVec(v) = sim.get(*expr) {
                let value = v.to_bit_str();
                println!("{name}@{step_id} = {value}")
            }
        }
    }

    // check outputs
    let mut output_iter = outputs.iter();
    if let Some(mut output) = output_iter.next() {
        for (cell_id, cell) in line.split(",").enumerate() {
            if cell_id == output.0 {
                // apply input
                let trimmed = cell.trim();
                if !trimmed.eq_ignore_ascii_case("x") {
                    let width = output.3;
                    let expected = BitVecValue::from_str_radix(trimmed, 10, width).unwrap();
                    let actual: BitVecValue = sim.get(output.1).try_into().unwrap();
                    assert_eq!(expected, actual, "{}@{step_id}", output.2);
                }

                // get next output
                if let Some(next_output) = output_iter.next() {
                    output = next_output;
                } else {
                    break;
                }
            }
        }
    }

    // advance simulation
    sim.step();
}
