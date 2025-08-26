// Copyright 2024 Cornell University
// Copyright 2024 Princeton University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

mod features;
mod samples;
mod summarize;

use crate::features::*;
use crate::samples::*;
use crate::summarize::bdd_summarize;
use baa::BitVecOps;
use clap::Parser;
use patronus::expr::*;
use patronus::mc::get_smt_value;
use patronus::smt::{CheckSatResponse, SolverContext};
use patronus_egraphs::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::io::Write;
use std::path::{Path, PathBuf};

#[derive(Parser, Debug)]
#[command(name = "patronus-egraphs-cond-synth")]
#[command(version)]
#[command(about = "Synthesizes rewrite conditions..", long_about = None)]
struct Args {
    #[arg(long, default_value = "8")]
    max_width: WidthInt,
    #[arg(long)]
    print_samples: bool,
    #[arg(long)]
    dump_smt: bool,
    #[arg(long)]
    bdd_formula: bool,
    #[arg(long, help = "checks the current condition of the re-write rules")]
    check_cond: bool,
    #[arg(
        long,
        help = "display up to N false negatives when checking conditions"
    )]
    show_false_negatives: Option<usize>,
    #[arg(long, help = "disable multi-threading")]
    single_thread: bool,
    #[arg(long, help = "write the generated assignments to a JSON file")]
    write_assignments: Option<PathBuf>,
    #[arg(
        long,
        help = "read assignments from a JSON file instead of generating and checking them"
    )]
    read_assignments: Option<PathBuf>,
    #[arg(long, help = "writes assignments and equivalence into a CSV table")]
    write_assignment_csv: Option<PathBuf>,
    #[arg(long, help = "writes features and equivalence into a CSV table")]
    write_feature_csv: Option<PathBuf>,
    #[arg(
        long,
        help = "writes features and equivalence into a PLA-style input file for espresso"
    )]
    write_espresso: Option<PathBuf>,
    #[arg(value_name = "RULE", index = 1)]
    rule: String,
}

fn main() {
    let args = Args::parse();

    // find rule and extract both sides
    let rewrites = create_rewrites();
    let rule = match rewrites.iter().find(|r| r.name() == args.rule) {
        Some(r) => r,
        None => {
            let available = rewrites.iter().map(|r| r.name()).collect::<Vec<_>>();
            panic!(
                "Failed to find rewrite rule `{}`!\nAvailable rules are: {:?}",
                args.rule, available
            );
        }
    };

    // generate and check samples
    let samples = if let Some(in_filename) = args.read_assignments {
        let file = std::fs::File::open(&in_filename).expect("failed to open input JSON");
        let mut reader = std::io::BufReader::new(file);
        let samples = Samples::from_json(&mut reader).expect("failed to parse input JSON");
        println!("Assignments loaded from {:?}", in_filename);
        samples
    } else {
        // remember start time
        let start = std::time::Instant::now();
        let samples = samples::generate_samples(
            rule,
            args.max_width,
            true,
            args.dump_smt,
            args.single_thread,
        );
        let delta_t = std::time::Instant::now() - start;
        println!(
            "Took {delta_t:?} on {} threads.",
            rayon::current_num_threads()
        );
        samples
    };

    println!("Found {} equivalent rewrites.", samples.num_equivalent());
    println!(
        "Found {} unequivalent rewrites.",
        samples.num_unequivalent()
    );

    let rule_info = get_rule_info(rule);

    if args.check_cond {
        check_conditions(rule, &samples, &rule_info, args.show_false_negatives);
    }

    if let Some(out_filename) = args.write_assignments {
        let mut file = std::fs::File::create(&out_filename).expect("failed to open output JSON");
        samples
            .clone()
            .to_json(&mut file)
            .expect("failed to write output JSON");
        println!("Wrote assignments to `{:?}`", out_filename);
    }

    if let Some(filename) = args.write_assignment_csv {
        write_assignment_csv(filename, &samples).expect("failed to write assignment CSV");
    }

    if args.print_samples {
        for sample in samples.iter() {
            println!("{:?}", sample);
        }
    }

    // check features
    let feature_start = std::time::Instant::now();
    let features = apply_features(&rule_info, &samples);
    let feature_delta_t = std::time::Instant::now() - feature_start;
    println!("{feature_delta_t:?} to apply all features");

    // outputs
    if let Some(filename) = args.write_feature_csv {
        write_feature_csv(filename, &features).expect("failed to write feature CSV");
    }

    if let Some(filename) = args.write_espresso {
        write_espresso(filename, &features).expect("failed to write espresso file");
    }

    if args.bdd_formula {
        let summarize_start = std::time::Instant::now();
        let formula = bdd_summarize(&features);
        let summarize_delta_t = std::time::Instant::now() - summarize_start;
        println!("Generated formula in {summarize_delta_t:?}:\n{}", formula);
    }
}

fn write_assignment_csv(filename: impl AsRef<Path>, samples: &Samples) -> std::io::Result<()> {
    let mut o = std::io::BufWriter::new(std::fs::File::create(filename)?);

    // header
    write!(o, "equivalent?,")?;
    let num_vars = samples.vars().count();
    for (ii, var) in samples.vars().enumerate() {
        write!(o, "{}", get_var_name(&var).unwrap())?;
        if ii < num_vars - 1 {
            write!(o, ",")?;
        }
    }
    writeln!(o)?;

    // data
    for (a, a_is_eq) in samples.iter() {
        write!(o, "{},", a_is_eq as u8)?;
        for (ii, (_var, value)) in a.iter().enumerate() {
            write!(o, "{}", *value)?;
            if ii < num_vars - 1 {
                write!(o, ",")?;
            }
        }
        writeln!(o)?;
    }

    Ok(())
}

fn write_feature_csv(filename: impl AsRef<Path>, features: &FeatureResult) -> std::io::Result<()> {
    let mut o = std::io::BufWriter::new(std::fs::File::create(filename)?);

    // header
    write!(o, "equivalent?,")?;
    let num_features = features.num_features();
    for (ii, feature) in features.labels().iter().enumerate() {
        write!(o, "{}", feature)?;
        if ii < num_features - 1 {
            write!(o, ",")?;
        }
    }
    writeln!(o)?;

    // data
    for (s, s_is_eq) in features.iter() {
        write!(o, "{},", s_is_eq as u8)?;
        for (ii, feature_on) in s.iter().enumerate() {
            let feature_on = *feature_on;
            write!(o, "{}", feature_on as u8)?;
            if ii < num_features - 1 {
                write!(o, ",")?;
            }
        }
        writeln!(o)?;
    }

    Ok(())
}

fn write_espresso(filename: impl AsRef<Path>, features: &FeatureResult) -> std::io::Result<()> {
    let mut o = std::io::BufWriter::new(std::fs::File::create(filename)?);

    // the inputs are the features
    writeln!(o, ".i {}", features.num_features())?;
    // the output is whether it is equivalent or not
    writeln!(o, ".o 1")?;

    for (features, is_eq) in features.iter() {
        for feature_on in features.iter() {
            write!(o, "{}", (*feature_on) as u8)?;
        }
        writeln!(o, " {}", is_eq as u8)?;
    }

    // end
    writeln!(o, ".e")?;

    Ok(())
}

fn check_conditions(
    rule: &ArithRewrite,
    samples: &Samples,
    info: &RuleInfo,
    show_false_negatives: Option<usize>,
) {
    // false positive => our current condition says it is equivalent, while it actually is not
    let mut false_positive = 0u64;
    // false negative => our current condition says the rule does not apply, while it actually could
    let mut false_negative = 0u64;
    let mut false_pos_examples = vec![];
    let mut false_neg_examples = vec![];
    for (a, is_eq) in samples.iter() {
        let condition_res = rule.eval_condition(&a);
        match (condition_res, is_eq) {
            (true, false) => {
                false_pos_examples.push(a);
                false_positive += 1;
            }
            (false, true) => {
                if show_false_negatives.is_some() {
                    false_neg_examples.push(a);
                }
                false_negative += 1;
            }
            _ => {} // ignore
        }
    }
    let num_total = samples.num_total() as f64;
    println!("The current implementation of the condition has:");
    println!(
        "False positives (BAD): {false_positive: >10} ({:.1}%)",
        (false_positive * 100) as f64 / num_total
    );
    println!(
        "False negatives (OK):  {false_negative: >10} ({:.1}%)",
        (false_negative * 100) as f64 / num_total
    );
    if !false_pos_examples.is_empty() {
        println!(
            "Some example assignments that are incorrectly classified as OK by our current condition:"
        );
        show_assignments(rule, info, &false_pos_examples, 10, CheckSatResponse::Sat);
    }
    if !false_neg_examples.is_empty() {
        println!(
            "Some example assignments that are incorrectly classified as DOES NOT APPLY by our current condition:"
        );
        show_assignments(
            rule,
            info,
            &false_neg_examples,
            show_false_negatives.unwrap(),
            CheckSatResponse::Unsat,
        );
    }
}

fn show_assignments(
    rule: &ArithRewrite,
    info: &RuleInfo,
    examples: &[Assignment],
    num_samples: usize,
    expected: CheckSatResponse,
) {
    let mut rnd = StdRng::seed_from_u64(0);
    let mut ctx = Context::default();
    let mut smt_ctx = start_solver(false);
    for _ in 0..num_samples {
        let a_idx = rnd.r#gen::<usize>() % examples.len();
        let a = &examples[a_idx];

        // generate smt expressions
        let (lhs, rhs) = rule.patterns();
        let substitution = gen_substitution(info, a);
        let lhs_egg = instantiate_pattern(lhs, &substitution);
        let rhs_egg = instantiate_pattern(rhs, &substitution);
        let lhs_expr = from_arith(&mut ctx, &lhs_egg);
        let rhs_expr = from_arith(&mut ctx, &rhs_egg);

        // run SMT solver to get a counter example
        smt_ctx.push().unwrap();
        let resp = check_eq(&mut ctx, &mut smt_ctx, lhs_expr, rhs_expr);
        assert_eq!(resp, expected);

        let equality = if resp == CheckSatResponse::Sat {
            "=/="
        } else {
            "=="
        };
        println!("- EGG: {} {equality} {}", lhs_egg, rhs_egg);
        println!(
            "  SMT: {} {equality} {}",
            lhs_expr.serialize_to_str(&ctx),
            rhs_expr.serialize_to_str(&ctx)
        );
        println!(
            "  ASN: {}",
            a.iter()
                .map(|(k, v)| format!("{k}={v}"))
                .collect::<Vec<_>>()
                .join(", ")
        );

        if resp == CheckSatResponse::Sat {
            // get assignments to variables
            let is_eq = ctx.equal(lhs_expr, rhs_expr);
            let vars = find_symbols_in_expr(&ctx, is_eq);
            let mut values: Vec<String> = vars
                .into_iter()
                .map(|v| {
                    let value = get_value(&mut ctx, &mut smt_ctx, v);
                    let name = ctx.get_symbol_name(v).unwrap();
                    format!("{name}={value}")
                })
                .collect();
            values.push(format!(
                "lhs_result={}",
                get_value(&mut ctx, &mut smt_ctx, lhs_expr)
            ));
            values.push(format!(
                "rhs_result={}",
                get_value(&mut ctx, &mut smt_ctx, rhs_expr)
            ));
            println!("    with: {}", values.join(", "));
        }
        smt_ctx.pop().unwrap();
    }
}

fn get_value(ctx: &mut Context, smt_ctx: &mut impl SolverContext, expr: ExprRef) -> String {
    let value = get_smt_value(ctx, smt_ctx, expr).unwrap();
    if let baa::Value::BitVec(v) = value {
        format!("{}", v.to_u64().unwrap())
    } else {
        unreachable!("no arrays!")
    }
}
