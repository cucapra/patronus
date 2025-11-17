use crate::ir::*;
use chumsky::Parser;
use chumsky::prelude::*;

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

#[derive(Clone, Debug, PartialEq)]
enum Token<'src> {
    Id(&'src str),
}
fn lexer<'src>() -> impl Parser<'src, &'src str, Vec<Token<'src>>> {}

fn expr_parser<'a>(m: &mut Module) -> impl Parser<'a, &'a str, ExprId> {
    let id = regex(r"[a-zA-Z_][a-zA-Z_0-9$]*").to(|name| m.push(Expr::Id));
    id
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

    #[test]
    fn parse_expr() {}
}
