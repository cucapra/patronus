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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_add_not() {
        let content = std::fs::read_to_string("inputs/AddNot.fir").unwrap();
    }
}
