// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::samples::{RuleInfo, Samples};
use egg::Var;
use patronus::expr::WidthInt;
use rustc_hash::FxHashMap;

/// generate a simplified re-write condition from samples, using BDDs
pub fn bdd_summarize(rule: &RuleInfo, samples: &Samples) -> String {
    // generate all labels and the corresponding BDD terminals
    let labels = get_labels(rule);
    let mut bdd = boolean_expression::BDD::<String>::new();
    let vars: Vec<_> = labels.iter().map(|ii| bdd.terminal(ii.clone())).collect();

    // start condition as trivially `false`
    let mut cond = boolean_expression::BDD_ZERO;
    for (assignment, is_equal) in samples.iter() {
        let v = FxHashMap::from_iter(assignment);
        let mut outputs = vec![];
        for feature in FEATURES.iter() {
            (feature.eval)(rule, &v, &mut outputs);
        }
        let lits = outputs
            .into_iter()
            .enumerate()
            .map(|(terminal, is_true)| {
                if is_true {
                    vars[terminal]
                } else {
                    bdd.not(vars[terminal])
                }
            })
            .collect::<Vec<_>>();
        let term = lits.into_iter().reduce(|a, b| bdd.and(a, b)).unwrap();
        let term = if is_equal { term } else { bdd.not(term) };

        cond = bdd.or(cond, term);
    }

    // extract simplified expression
    format!("{:?}", bdd.to_expr(cond))
}

fn get_labels(rule: &RuleInfo) -> Vec<String> {
    FEATURES
        .iter()
        .map(|f| (f.labels)(rule))
        .reduce(|mut a, mut b| {
            a.append(&mut b);
            a
        })
        .unwrap_or_default()
}

const FEATURES: &[Feature] = &[
    Feature {
        name: "is_unsigned", // (13)
        labels: |r| {
            let mut o = vec![];
            for sign in r.signs() {
                o.push(format!("!{sign}"));
            }
            o
        },
        eval: |r, v, o| {
            for sign in r.signs() {
                // s_i == unsign
                o.push(v[&sign] == 0);
            }
        },
    },
    Feature {
        name: "is_width_equal", // (14)
        labels: |r| {
            let mut o = vec![];
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        o.push(format!("{w_i} == {w_j}"));
                    }
                }
            }
            o
        },
        eval: |r, v, o| {
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        // w_i == w_j
                        o.push(v[&w_i] == v[&w_j]);
                    }
                }
            }
        },
    },
    Feature {
        name: "is_width_smaller", // (15) + (16)
        labels: |r| {
            let mut o = vec![];
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        o.push(format!("{w_i} < {w_j}"));
                        o.push(format!("{w_i} + 1 < {w_j}"));
                        o.push(format!("{w_i} - 1 < {w_j}"));
                    }
                }
            }
            o
        },
        eval: |r, v, o| {
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        let (w_i, w_j) = (v[&w_i], v[&w_j]);
                        // w_i < w_j
                        o.push(w_i < w_j);
                        // w_i + 1 < w_j
                        o.push(w_i + 1 < w_j);
                        // w_i - 1 < w_j
                        o.push(w_i - 1 < w_j);
                    }
                }
            }
        },
    },
    Feature {
        name: "is_width_sum_smaller", // (17) + (18)
        labels: |r| {
            let mut o = vec![];
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        for w_k in r.widths() {
                            if w_k != w_i && w_k != w_j {
                                o.push(format!("{w_i} + {w_j} < {w_k}"));
                                o.push(format!("{w_i} as u64 + 2u64.pow({w_j}) < {w_k} as u64"));
                            }
                        }
                    }
                }
            }
            o
        },
        eval: |r, v, o| {
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        for w_k in r.widths() {
                            if w_k != w_i && w_k != w_j {
                                let (w_i, w_j, w_k) = (v[&w_i], v[&w_j], v[&w_k]);
                                // w_i + w_j < w_k
                                o.push(w_i + w_j < w_k);
                                // w_i + 2**w_j < w_k
                                o.push(w_i as u64 + 2u64.pow(w_j) < w_k as u64);
                            }
                        }
                    }
                }
            }
        },
    },
];

struct Feature {
    name: &'static str,
    labels: fn(rule: &RuleInfo) -> Vec<String>,
    eval: fn(rule: &RuleInfo, v: &FxHashMap<Var, WidthInt>, out: &mut Vec<bool>),
}
