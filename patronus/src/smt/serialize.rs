// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, Expr, ExprRef, ForEachChild, Type, TypeCheck};
use crate::smt::solver::SmtCommand;
use baa::BitVecOps;
use std::io::Write;

pub type Result<T> = std::io::Result<T>;

pub fn serialize_expr(out: &mut impl Write, ctx: &Context, expr: ExprRef) -> Result<()> {
    // we need to visit each expression "number of children + 1" times
    let mut todo: Vec<(ExprRef, u32, bool)> = vec![(expr, 0, false)];

    // analyze uses to print out DAG in linear size using let expressions
    // let uses =

    while let Some((e, pc, must_be_bit_vec)) = todo.pop() {
        let expr = &ctx[e];
        let result_is_1_bit = e.get_bv_type(ctx) == Some(1);
        let result_is_bit_vec = always_produces_bit_vec(expr);

        let convert_result_to_bv = result_is_1_bit && must_be_bit_vec && !result_is_bit_vec;
        let convert_result_to_bool = result_is_1_bit && !must_be_bit_vec && result_is_bit_vec;
        debug_assert!(!(convert_result_to_bv && convert_result_to_bool));

        if pc == 0 {
            if convert_result_to_bv {
                // 1-bit results are normally bool, we need to convert them to bit-vec
                write!(out, "(ite ")?;
            }
            if convert_result_to_bool {
                write!(out, "(= ")?;
            }

            // first time we visit
            match expr {
                Expr::BVSymbol { name, .. } => {
                    write!(out, "{}", escape_smt_identifier(&ctx[*name]))?;
                }
                Expr::BVLiteral(v) => {
                    let value = v.get(ctx);
                    if value.width() > 1 {
                        write!(out, "#b{}", v.get(ctx).to_bit_str())?;
                    } else if value.is_true() {
                        write!(out, "true")?;
                    } else {
                        debug_assert!(value.is_false());
                        write!(out, "false")?;
                    }
                }
                Expr::BVZeroExt { e, by, .. } => {
                    debug_assert!(*by > 0);
                    let width = e.get_bv_type(ctx).expect("zext only works on bv expr");
                    if width == 1 {
                        // this encoding avoids the zext by using an ite on the expanded true/false case
                        write!(out, "(ite ")?;
                    } else {
                        write!(out, "((_ zero_extend {by}) ")?;
                    }
                }
                Expr::BVSignExt { by, .. } => {
                    debug_assert!(*by > 0);
                    write!(out, "((_ sign_extend {by}) ")?;
                }
                Expr::BVSlice { e, hi, lo } => {
                    let width = e.get_bv_type(ctx).expect("slice only works on bv expr");
                    // skip no-op bit extracts (this helps us avoid slices on boolean values)
                    if *lo == 0 && width - 1 == *hi {
                        // nothing to do
                    } else {
                        write!(out, "((_ extract {hi} {lo}) ")?;
                    }
                }
                Expr::BVNot(e, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(not ")?;
                    } else {
                        write!(out, "(bvnot ")?;
                    }
                }
                Expr::BVNegate(_, _) => {
                    write!(out, "(bvneg ")?;
                }
                Expr::BVEqual(_, _) => {
                    write!(out, "(= ")?;
                }
                Expr::BVImplies(a, b) => {
                    debug_assert!(a.get_type(ctx).is_bool());
                    debug_assert!(b.get_type(ctx).is_bool());
                    write!(out, "(=> ")?;
                }
                Expr::BVGreater(_, _) => {
                    write!(out, "(bvugt ")?;
                }
                Expr::BVGreaterSigned(_, _, _) => {
                    write!(out, "(bvsgt ")?;
                }
                Expr::BVGreaterEqual(_, _) => {
                    write!(out, "(bvuge ")?;
                }
                Expr::BVGreaterEqualSigned(_, _, _) => {
                    write!(out, "(bvsge ")?;
                }
                Expr::BVConcat(_, _, _) => {
                    write!(out, "(concat ")?;
                }
                Expr::BVAnd(_, _, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(and ")?;
                    } else {
                        write!(out, "(bvand ")?;
                    }
                }
                Expr::BVOr(_, _, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(or ")?;
                    } else {
                        write!(out, "(bvor ")?;
                    }
                }
                Expr::BVXor(_, _, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(xor ")?;
                    } else {
                        write!(out, "(bvxor ")?;
                    }
                }
                Expr::BVShiftLeft(_, _, _) => {
                    write!(out, "(bvshl ")?;
                }
                Expr::BVArithmeticShiftRight(_, _, _) => {
                    write!(out, "(bvashr ")?;
                }
                Expr::BVShiftRight(_, _, _) => {
                    write!(out, "(bvlshr ")?;
                }
                Expr::BVAdd(_, _, _) => {
                    write!(out, "(bvadd ")?;
                }
                Expr::BVMul(_, _, _) => {
                    write!(out, "(bvmul ")?;
                }
                Expr::BVSignedDiv(_, _, _) => {
                    write!(out, "(bvsdiv ")?;
                }
                Expr::BVUnsignedDiv(_, _, _) => {
                    write!(out, "(bvudiv ")?;
                }
                Expr::BVSignedMod(_, _, _) => {
                    write!(out, "(bvsmod ")?;
                }
                Expr::BVSignedRem(_, _, _) => {
                    write!(out, "(bvsrem ")?;
                }
                Expr::BVUnsignedRem(_, _, _) => {
                    write!(out, "(bvurem ")?;
                }
                Expr::BVSub(_, _, _) => {
                    write!(out, "(bvsub ")?;
                }
                Expr::BVArrayRead { .. } => {
                    write!(out, "(select ")?;
                }
                Expr::BVIte { .. } => {
                    write!(out, "(ite ")?;
                }
                Expr::ArraySymbol { name, .. } => {
                    write!(out, "{}", escape_smt_identifier(&ctx[*name]))?;
                }
                Expr::ArrayConstant { .. } => {
                    write!(out, "((as const ")?;
                    let tpe = expr.get_type(ctx);
                    serialize_type(out, tpe)?;
                    write!(out, ") ")?;
                }
                Expr::ArrayEqual(_, _) => {
                    write!(out, "(= ")?;
                }
                Expr::ArrayStore { .. } => {
                    write!(out, "(store ")?;
                }
                Expr::ArrayIte { .. } => {
                    write!(out, "(ite ")?;
                }
            }
        }

        let child_must_be_bit_vec = always_consumes_bit_vec(expr);

        if let Some(next_child) = find_next_child(pc, expr) {
            write!(out, " ")?;
            todo.push((e, pc + 1, must_be_bit_vec));
            todo.push((next_child, 0, child_must_be_bit_vec));
        } else {
            // we had to serialize some children first => we need a closing parenthesis
            if pc > 0 {
                // special continuation for zero extend of booleans (for which we use an ite)
                if let Expr::BVZeroExt { e, by, .. } = expr
                    && e.get_type(ctx).is_bool()
                {
                    let zeros = "0".repeat(*by as usize);
                    write!(out, " #b{}1 #b{}0", zeros, zeros)?;
                }
                // everyone gets a closing parenthesis
                write!(out, ")")?;
            }
            if convert_result_to_bv {
                // 1-bit results are normally bool, we need to convert them to bit-vec
                write!(out, " #b1 #b0)")?;
            }
            if convert_result_to_bool {
                // .. == 1?
                write!(out, " #b1)")?;
            }
        }
    }
    Ok(())
}

/// Returns whether the expressions always consumes bit vectors, even with 1-bit arguments
fn always_consumes_bit_vec(e: &Expr) -> bool {
    match e {
        // sign extension could be implemented with an ite similar to zext, but is currently not
        Expr::BVSignExt { .. }
        // arithmetic and comparison operators are not implemented on booleans
        | Expr::BVNegate(_, _)
        | Expr::BVGreater(_, _)
        | Expr::BVGreaterSigned(_, _, _)
        | Expr::BVGreaterEqual(_, _)
        | Expr::BVGreaterEqualSigned(_, _, _)
        | Expr::BVConcat(_, _, _)
        | Expr::BVShiftLeft(_, _, _)
        | Expr::BVArithmeticShiftRight(_, _, _)
        | Expr::BVShiftRight(_, _, _)
        | Expr::BVAdd(_, _, _)
        | Expr::BVMul(_, _, _)
        | Expr::BVSignedDiv(_, _, _)
        | Expr::BVUnsignedDiv(_, _, _)
        | Expr::BVSignedMod(_, _, _)
        | Expr::BVSignedRem(_, _, _)
        | Expr::BVUnsignedRem(_, _, _)
        | Expr::BVSub(_, _, _) => true,
        _ => false,
    }
}

/// Returns whether the expressions always produces bit vectors, even when the return type is 1-bit
fn always_produces_bit_vec(e: &Expr) -> bool {
    match e {
        // sign and zero extension and concat will always yield a result of size 2-bit or wider
        Expr::BVZeroExt { .. }
        | Expr::BVSignExt { .. }
        | Expr::BVConcat(_, _, _)
        // a 1-bit slice will produce a bit-vector
        | Expr::BVSlice { .. }
        // arithmetic operators are not implemented on booleans
        | Expr::BVNegate(_, _)
        | Expr::BVShiftLeft(_, _, _)
        | Expr::BVArithmeticShiftRight(_, _, _)
        | Expr::BVShiftRight(_, _, _)
        | Expr::BVAdd(_, _, _)
        | Expr::BVMul(_, _, _)
        | Expr::BVSignedDiv(_, _, _)
        | Expr::BVUnsignedDiv(_, _, _)
        | Expr::BVSignedMod(_, _, _)
        | Expr::BVSignedRem(_, _, _)
        | Expr::BVUnsignedRem(_, _, _)
        | Expr::BVSub(_, _, _) => true,
        // note that comparisons will always produce booleans
        _ => false,
    }
}

fn find_next_child(pos: u32, e: &Expr) -> Option<ExprRef> {
    let mut count = 0;
    let mut out = None;
    e.for_each_child(|c| {
        if count == pos {
            out = Some(*c);
        }
        count += 1;
    });
    out
}

pub fn serialize_cmd(out: &mut impl Write, ctx: Option<&Context>, cmd: &SmtCommand) -> Result<()> {
    match cmd {
        SmtCommand::Exit => writeln!(out, "(exit)"),
        SmtCommand::CheckSat => writeln!(out, "(check-sat)"),
        SmtCommand::Reset => writeln!(out, "(reset)"),
        SmtCommand::SetLogic(logic) => writeln!(out, "(set-logic {})", logic.to_smt_str()),
        SmtCommand::SetOption(name, value) => {
            writeln!(out, "(set-option :{name} {})", escape_smt_identifier(value))
        }
        SmtCommand::SetInfo(name, value) => {
            writeln!(out, "(set-option :{name} {})", escape_smt_identifier(value))
        }
        SmtCommand::Assert(e) => {
            write!(out, "(assert ")?;
            serialize_expr(out, ctx.unwrap(), *e)?;
            writeln!(out, ")")
        }
        SmtCommand::DeclareConst(symbol) => {
            let ctx = ctx.unwrap();
            write!(
                out,
                "(declare-const {} ",
                escape_smt_identifier(ctx.get_symbol_name(*symbol).unwrap())
            )?;
            serialize_type(out, symbol.get_type(ctx))?;
            writeln!(out, ")")
        }
        SmtCommand::DefineConst(symbol, value) => {
            let ctx = ctx.unwrap();
            // name, then empty arguments
            write!(
                out,
                "(define-fun {} () ",
                escape_smt_identifier(ctx.get_symbol_name(*symbol).unwrap())
            )?;
            serialize_type(out, symbol.get_type(ctx))?;
            write!(out, " ")?;
            serialize_expr(out, ctx, *value)?;
            writeln!(out, ")")
        }
        SmtCommand::CheckSatAssuming(exprs) => {
            let ctx = ctx.unwrap();
            write!(out, "(check-sat-assuming (")?;
            for &e in exprs.iter() {
                serialize_expr(out, ctx, e)?;
                write!(out, " ")?;
            }
            writeln!(out, "))")
        }
        SmtCommand::Push(n) => writeln!(out, "(push {n})"),
        SmtCommand::Pop(n) => writeln!(out, "(pop {n})"),
        SmtCommand::GetValue(e) => {
            let ctx = ctx.unwrap();
            write!(out, "(get-value (")?;
            serialize_expr(out, ctx, *e)?;
            writeln!(out, "))")
        }
    }
}

pub fn serialize_type(out: &mut impl Write, tpe: Type) -> Result<()> {
    match tpe {
        Type::BV(1) => write!(out, "Bool"),
        Type::BV(width) => write!(out, "(_ BitVec {width})"),
        Type::Array(a) => match (a.index_width, a.data_width) {
            (1, 1) => write!(out, "(Array Bool Bool)"),
            (1, d) => write!(out, "(Array Bool (_ BitVec {d}))"),
            (i, 1) => write!(out, "(Array (_ BitVec {i}) Bool)"),
            (i, d) => write!(out, "(Array (_ BitVec {i}) (_ BitVec {d}))"),
        },
    }
}

/// See <simple_symbol> definition in the Concrete Syntax Appendix of the SMTLib Spec
fn is_simple_smt_identifier(id: &str) -> bool {
    if id.is_empty() {
        return false; // needs to be non-empty
    }
    let mut is_first = true;
    for cc in id.chars() {
        if !cc.is_ascii() {
            return false; // all allowed characters are ASCII characters
        }
        let ac = cc as u8;
        let is_alpha = ac.is_ascii_uppercase() || ac.is_ascii_lowercase();
        let is_num = ac.is_ascii_digit();
        let is_other_allowed_char = matches!(
            ac,
            b'+' | b'-'
                | b'/'
                | b'*'
                | b'='
                | b'%'
                | b'?'
                | b'!'
                | b'.'
                | b'$'
                | b'_'
                | b'~'
                | b'&'
                | b'^'
                | b'<'
                | b'>'
                | b'@'
        );
        if !(is_alpha | is_num | is_other_allowed_char) {
            return false;
        }
        if is_num && is_first {
            return false; // the first character is not allowed ot be a digit
        }
        is_first = false;
    }
    true // passed all checks
}

fn escape_smt_identifier(id: &str) -> std::borrow::Cow<'_, str> {
    if is_simple_smt_identifier(id) {
        std::borrow::Cow::Borrowed(id)
    } else {
        let escaped = format!("|{}|", id);
        std::borrow::Cow::Owned(escaped)
    }
}

#[cfg(test)]
fn unescape_smt_identifier(id: &str) -> &str {
    if id.starts_with("|") {
        assert!(id.ends_with("|"));
        &id[1..id.len() - 1]
    } else {
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ArrayType;

    #[test]
    fn test_our_escaping() {
        assert_eq!(
            unescape_smt_identifier(&escape_smt_identifier("a b")),
            "a b"
        );
    }

    #[test]
    fn test_serialize_symbols() {
        let mut ctx = Context::default();
        let sym = ctx.bv_symbol("$auto$async2sync.cc:262:execute$65@20", 4);
        assert_eq!(s_expr(&ctx, sym), "|$auto$async2sync.cc:262:execute$65@20|");
    }

    #[test]
    fn test_serialize_declare_const() {
        let mut ctx = Context::default();
        let sym = ctx.bv_symbol("$auto$async2sync.cc:262:execute$65@20", 4);
        let cmd = SmtCommand::DeclareConst(sym);
        // we need to ensure that symbol names are properly escaped!
        assert_eq!(
            s_cmd(&ctx, &cmd),
            "(declare-const |$auto$async2sync.cc:262:execute$65@20| (_ BitVec 4))\n"
        );
    }

    fn s_type(t: Type) -> String {
        let mut out = Vec::new();
        serialize_type(&mut out, t).unwrap();
        String::from_utf8(out).unwrap()
    }

    fn s_expr(ctx: &Context, e: ExprRef) -> String {
        let mut out = Vec::new();
        serialize_expr(&mut out, ctx, e).unwrap();
        String::from_utf8(out).unwrap()
    }

    fn s_cmd(ctx: &Context, cmd: &SmtCommand) -> String {
        let mut out = Vec::new();
        serialize_cmd(&mut out, Some(ctx), cmd).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn test_serialize_types() {
        assert_eq!(s_type(Type::BV(1)), "Bool");
        assert_eq!(s_type(Type::BV(2)), "(_ BitVec 2)");
        assert_eq!(s_type(Type::BV(123)), "(_ BitVec 123)");
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 3,
                data_width: 5,
            })),
            "(Array (_ BitVec 3) (_ BitVec 5))"
        );
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 1,
                data_width: 5,
            })),
            "(Array Bool (_ BitVec 5))"
        );
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 3,
                data_width: 1,
            })),
            "(Array (_ BitVec 3) Bool)"
        );
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 1,
                data_width: 1,
            })),
            "(Array Bool Bool)"
        );
    }

    #[test]
    fn test_serialize_nullary_expr() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("a", 2);
        assert_eq!(s_expr(&ctx, a), "a");
        assert_eq!(s_expr(&ctx, ctx.get_false()), "false");
        assert_eq!(s_expr(&ctx, ctx.get_true()), "true");
        let bv_lit = ctx.bit_vec_val(3, 3);
        assert_eq!(s_expr(&ctx, bv_lit), "#b011");
    }

    #[test]
    fn test_serialize_dag() {}
}
