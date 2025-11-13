use lalrpop_util::lalrpop_mod;
use patronus::expr::{StringRef, WidthInt};
use std::num::NonZeroU32;

lalrpop_mod!(firrtl);

#[derive(Debug)]
pub struct Circuit {
    name: StringRef,
    modules: Vec<Module>,
}

#[derive(Debug)]
pub struct Module {
    name: StringRef,
    ports: Vec<Port>,
    body: StmtId,
}

#[derive(Debug, Clone)]
pub struct Port {
    name: StringRef,
    direction: Direction,
    tpe: Type,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Direction {
    Input,
    Output,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Wire {
        name: StringRef,
        tpe: Type,
    },
    Register {
        name: StringRef,
        tpe: Type,
        clock: ExprId,
        reset: ExprId,
        init: ExprId,
    },
    Instance {
        name: StringRef,
        module: StringRef,
    },
    Memory {
        name: StringRef,
        data_type: Type,
        depth: u64,
        write_latency: u16,
        read_latency: u16,
        ports: Vec<MemPort>,
        ruw: ReadUnderWrite,
    },
    Node {
        name: StringRef,
        value: ExprId,
    },
    When {
        cond: ExprId,
        tru: StmtId,
        fals: StmtId,
    },
    Block(Vec<StmtId>),
    Connect {
        lhs: StringRef,
        rhs: ExprId,
    },
    ConnectInvalid {
        lhs: StringRef,
    },
    Stop {
        clk: ExprId,
        en: ExprId,
        ret: i32,
    },
}

#[derive(Debug, Copy, Clone)]
pub struct MemPort {
    name: StringRef,
    read: bool,
    write: bool,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ReadUnderWrite {
    Undefined,
    Old,
    New,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Expr {}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Type {
    UInt(WidthInt),
    SInt(WidthInt),
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct StmtId(NonZeroU32);

impl StmtId {
    pub fn from_index(index: usize) -> Self {
        Self(NonZeroU32::new(index as u32 + 1).unwrap())
    }
    pub fn index(&self) -> usize {
        (self.0.get() - 1) as usize
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ExprId(NonZeroU32);

impl ExprId {
    pub fn from_index(index: usize) -> Self {
        Self(NonZeroU32::new(index as u32 + 1).unwrap())
    }
    pub fn index(&self) -> usize {
        (self.0.get() - 1) as usize
    }
}

/// Quick scan over the FIRRTL to find the name of the circuit and the string slice for each module.
fn find_modules(source: &str) -> (&str, Vec<&str>) {
    let mut circuit = "";
    let mut indent = "";
    let mut module_start = 0usize;
    let mut modules = vec![];
    for line in source.lines() {
        if circuit.is_empty() {
            let line = line.trim();
            // searching for a circuit
            if line.starts_with("circuit") {
                let name = line["circuit".len()..].trim();
                debug_assert!(name.ends_with(':'));
                let name = name[..name.len() - 1].trim();
                circuit = name;
            }
        } else {
            // searching for modules
            let line_offset = line.as_ptr() as usize - source.as_ptr() as usize;
            let line_trimmed = line.trim();
            if line_trimmed.starts_with("module") {
                let new_indent = &line[0..line.len() - line_trimmed.len()];
                if module_start > 0 {
                    modules.push(&source[module_start..line_offset]);
                    debug_assert_eq!(new_indent, indent);
                }
                indent = new_indent;
                module_start = line_offset;
            }
        }
    }
    debug_assert!(module_start > 0, "no modules found");
    modules.push(&source[module_start..]);
    debug_assert!(!modules.is_empty(), "no modules found");
    (circuit, modules)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_add_not() {
        let src = std::fs::read_to_string("inputs/AddNot.fir").unwrap();
        let (circuit, modules) = find_modules(&src);
        assert_eq!(circuit, "AddNot");
        assert_eq!(modules.len(), 1);
        assert_eq!(modules[0].lines().next().unwrap().trim(), "module AddNot:");
    }
}
