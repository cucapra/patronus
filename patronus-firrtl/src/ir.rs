// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use cranelift_entity::{EntityRef, PrimaryMap};
use patronus::expr::{StringRef, WidthInt};
use rustc_hash::FxBuildHasher;
use std::num::NonZeroU32;
use std::ops::Index;

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
    stmts: PrimaryMap<StmtId, Stmt>,
    exprs: PrimaryMap<ExprId, Expr>,
    strings: indexmap::IndexSet<String, FxBuildHasher>,
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
pub enum Expr {
    Reference(StringRef),
}

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

impl EntityRef for StmtId {
    fn new(index: usize) -> Self {
        Self::from_index(index)
    }
    fn index(self) -> usize {
        Self::index(&self)
    }
}

impl EntityRef for ExprId {
    fn new(index: usize) -> Self {
        Self::from_index(index)
    }
    fn index(self) -> usize {
        Self::index(&self)
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

impl Index<ExprId> for Module {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index]
    }
}

impl Index<StmtId> for Module {
    type Output = Stmt;

    fn index(&self, index: StmtId) -> &Self::Output {
        &self.stmts[index]
    }
}

pub trait PushEntity<Element: ?Sized> {
    type Id: ?Sized + Clone + Copy;
    fn push(&mut self, element: Element) -> Self::Id;
}

impl PushEntity<Expr> for Module {
    type Id = ExprId;
    fn push(&mut self, element: Expr) -> Self::Id {
        self.exprs.push(element)
    }
}

impl PushEntity<Stmt> for Module {
    type Id = StmtId;
    fn push(&mut self, element: Stmt) -> Self::Id {
        self.stmts.push(element)
    }
}
