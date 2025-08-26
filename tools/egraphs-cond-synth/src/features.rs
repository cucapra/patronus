// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::samples::{RuleInfo, Samples, get_var_name};
use bitvec::prelude as bv;
use egg::Var;
use patronus::expr::WidthInt;
use rustc_hash::FxHashMap;

/// Applies the features from the ROVER paper to all assignments and returns the result.
pub fn apply_features(rule: &RuleInfo, samples: &Samples) -> FeatureResult {
    let labels = get_labels(rule);
    let mut results = bv::BitVec::new();

    for (assignment, is_equal) in samples.iter() {
        let v = FxHashMap::from_iter(assignment);
        results.push(is_equal);
        for feature in FEATURES.iter() {
            (feature.eval)(rule, &v, &mut results);
        }
    }

    FeatureResult { labels, results }
}

pub struct FeatureResult {
    labels: Vec<String>,
    results: bv::BitVec,
}

impl FeatureResult {
    pub fn num_features(&self) -> usize {
        self.labels.len()
    }
    pub fn labels(&self) -> &[String] {
        &self.labels
    }
    pub fn iter(&self) -> impl Iterator<Item = (&bv::BitSlice, bool)> + '_ {
        let cs = self.num_features() + 1;
        self.results.chunks(cs).map(|c| {
            let is_equivalent = c[0];
            let features = &c[1..];
            (features, is_equivalent)
        })
    }
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
                o.push(format!("!{}", get_var_name(&sign).unwrap()));
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
                        o.push(format!(
                            "{} == {}",
                            get_var_name(&w_i).unwrap(),
                            get_var_name(&w_j).unwrap(),
                        ));
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
                        let w_i = get_var_name(&w_i).unwrap();
                        let w_j = get_var_name(&w_j).unwrap();
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
                                let w_i = get_var_name(&w_i).unwrap();
                                let w_j = get_var_name(&w_j).unwrap();
                                let w_k = get_var_name(&w_k).unwrap();
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
    #[allow(dead_code)]
    name: &'static str,
    labels: fn(rule: &RuleInfo) -> Vec<String>,
    eval: fn(rule: &RuleInfo, v: &FxHashMap<Var, WidthInt>, out: &mut bv::BitVec),
}
