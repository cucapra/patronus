// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprRef, TypeCheck};
use crate::system::TransitionSystem;
use baa::{BitVecOps, BitVecValue};
use fst_writer::{
    FstBodyWriter, FstFileType, FstInfo, FstScopeType, FstSignalId, FstSignalType, FstVarDirection,
    FstVarType, FstWriteError,
};
use rustc_hash::FxHashMap;
use std::fs::File;
use std::io::BufWriter;
use std::path::Path;

pub struct Wavedump {
    out: Option<FstBodyWriter<BufWriter<File>>>,
    signals: Vec<(ExprRef, FstSignalId)>,
}

#[derive(Debug)]
#[allow(dead_code)]
pub enum WavedumpError {
    FstError(String),
}

impl From<fst_writer::FstWriteError> for WavedumpError {
    fn from(value: FstWriteError) -> Self {
        WavedumpError::FstError(value.to_string())
    }
}

pub type Result<T> = std::result::Result<T, WavedumpError>;

impl Wavedump {
    pub fn open_fst(
        filename: impl AsRef<Path>,
        ctx: &Context,
        sys: &TransitionSystem,
    ) -> Result<Self> {
        let info = FstInfo {
            start_time: 0,
            timescale_exponent: 0,
            version: "Patronus system interpreter".to_string(),
            date: "".to_string(),
            file_type: FstFileType::Verilog,
        };
        let mut header = fst_writer::open_fst(filename, &info)?;

        // generate signal declarations for DUT
        if !sys.name.is_empty() {
            header.scope(&sys.name, &sys.name, FstScopeType::Module)?;
        }

        let mut vars: Vec<_> = sys.get_name_map(ctx).into_iter().collect();
        vars.sort();
        let mut signal_map = FxHashMap::default();
        for (s, e) in vars.into_iter() {
            if let Some(bits) = ctx[e].get_bv_type(ctx) {
                let parts: Vec<_> = s.split('.').collect();
                let num_scopes = parts.len() - 1;
                for (id, scope) in parts.iter().enumerate() {
                    if id < num_scopes {
                        header.scope(scope, "", FstScopeType::Module)?;
                    }
                }

                let alias = signal_map.get(&e).cloned();

                // TODO: detect already know expressions
                let id = header.var(
                    parts.last().unwrap(),
                    FstSignalType::bit_vec(bits),
                    FstVarType::Wire,
                    FstVarDirection::Implicit,
                    alias,
                )?;
                if alias.is_none() {
                    signal_map.insert(e, id);
                }

                for _ in 0..num_scopes {
                    header.up_scope()?;
                }
            }
        }

        if !sys.name.is_empty() {
            header.up_scope()?;
        }

        let signals = signal_map.into_iter().collect();

        let mut out = header.finish()?;
        out.time_change(0)?;
        Ok(Self {
            out: Some(out),
            signals,
        })
    }

    pub fn signals(&self) -> Vec<ExprRef> {
        self.signals.iter().map(|(e, _)| *e).collect()
    }

    pub fn dump_signals(&mut self, values: Vec<Option<BitVecValue>>, time: u64) -> Result<()> {
        if let Some(out) = self.out.as_mut() {
            for ((_, id), value) in self.signals.iter().zip(values.into_iter()) {
                if let Some(bv) = value {
                    out.signal_change(*id, bv.to_bit_str().as_bytes())?;
                }
            }
            out.time_change(time + 1)?;
        }
        Ok(())
    }
}

impl Drop for Wavedump {
    fn drop(&mut self) {
        let writer = std::mem::take(&mut self.out);
        if let Some(writer) = writer {
            writer.finish().unwrap();
        }
    }
}
