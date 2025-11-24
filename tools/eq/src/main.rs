// Copyright 2025 Cornell University
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
#[command(name = "eq")]
#[command(author = "Kevin Laeufer <laeufer@cornell.edu>")]
#[command(version)]
#[command(about = "Checks two btor files for equivalence.", long_about = None)]
struct Args {
    #[arg(value_name = "BTOR2_A", index = 1)]
    a: String,
    #[arg(value_name = "BTOR2_B", index = 2)]
    b: String,
}

fn main() {
    let args = Args::parse();
    let mut ctx = Context::default();
    let sys_a =
        btor2::parse_file_with_ctx(&args.a, &mut ctx).expect("Failed to load btor2 A file!");
    let sys_b =
        btor2::parse_file_with_ctx(&args.b, &mut ctx).expect("Failed to load btor2 B file!");
}

fn make_miter(
    ctx: &mut Context,
    mut sys_a: TransitionSystem,
    mut sys_b: TransitionSystem,
) -> TransitionSystem {
    prefix_symbols(ctx, &mut sys_a, "A_");
    prefix_symbols(ctx, &mut sys_b, "B_");
}

fn prefix_symbols(ctx: &mut Context, sys: &mut TransitionSystem, prefix: &str) {
    sys.update_expressions(|a| {
        if ctx[a].is_symbol() {
            let new_name = format!("{prefix}{}", ctx[a].get_symbol_name(ctx).unwrap());
            let new_name_ref = ctx.string(new_name.into());
            let tpe = a.get_type(ctx);
            let new_symbol = ctx.symbol(new_name_ref, tpe);
            Some(new_symbol)
        } else {
            None
        }
    });
}
