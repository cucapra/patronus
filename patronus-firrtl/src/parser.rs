use crate::ir::*;
use chumsky::Parser;
use chumsky::prelude::*;
use logos::Logos;

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

// #[derive(Clone, Debug, PartialEq)]
// enum Token<'src> {
//     Id(&'src str),
//     RelaxedId(&'src str),
//     FileInfo(&'src str),
//     UnsignedInt(&'src str),
//     SignedInt(&'src str),
//     HexLit(&'src str),
//     BinaryLit(&'src str),
//     Keyword(&'src str),
//     Indent,
//     Dedent,
// }

// const KEYWORDS: [&str; 51] = [
//     "circuit",
//     "module",
//     "extmodule",
//     "parameter",
//     "input",
//     "output",
//     "UInt",
//     "SInt",
//     "Clock",
//     "Reset",
//     "AsyncReset",
//     "Analog",
//     "Fixed",
//     "Interval",
//     "flip",
//     "wire",
//     "reg",
//     "with",
//     "reset",
//     "mem",
//     "depth",
//     "reader",
//     "writer",
//     "readwriter",
//     "inst",
//     "of",
//     "node",
//     "is",
//     "invalid",
//     "when",
//     "else",
//     "stop",
//     "printf",
//     "skip",
//     "old",
//     "new",
//     "undefined",
//     "mux",
//     "validif",
//     "cmem",
//     "smem",
//     "mport",
//     "infer",
//     "read",
//     "write",
//     "rdwr",
//     "attach",
//     "assert",
//     "assume",
//     "cover",
//     "version"
// ];

// fn lexer<'src>() -> impl Parser<'src, &'src str, Vec<Token<'src>>> {
//     let id = regex(r"[a-zA-Z_][a-zA-Z_0-9$]*").map(Token::Id);
//     let relaxed_id = regex(r"[a-zA-Z_0-9$]+").map(Token::RelaxedId);
//     //let file_info = regex(r"@\[\s*([^\]]*)\s*\]").map(Token::FileInfo);
//     // let whitespace = one_of(" \t\r\n");
//     let file_info = just("@[")
//         .ignore_then(
//             none_of(']')
//                 .repeated()
//                 .at_least(1)
//                 .to_slice()
//                 .map(|s: &str| Token::FileInfo(s.trim())),
//         )
//         .then_ignore(just(']'));
//     let keywords = one_of(KEYWORDS.iter()).map(Token::Keyword);
//
//     // important: check ID first
//     let token = keywords.or(id).or(relaxed_id).or(file_info);
//
//     token.repeated().collect()
// }

// fn expr_parser<'a>(m: &mut Module) -> impl Parser<'a, &'a str, ExprId> {
//     // let id = regex(r"[a-zA-Z_][a-zA-Z_0-9$]*").to(|name| m.push(Expr::Id));
//     // id
//     todo!()
// }

#[derive(Logos, Debug, PartialEq, Eq, Hash, Clone)]
enum Token {
    #[token(
        "(circuit)|(module)|(extmodule)|(parameter)|(input)|(output)|(UInt)|(SInt)|(Clock)|(Reset)|(AsyncReset)|(Analog)|(Fixed)|(Interval)|(flip)|(wire)|(reg)|(with)|(reset)|(mem)|(depth)|(reader)|(writer)|(readwriter)|(inst)|(of)|(node)|(is)|(invalid)|(when)|(else)|(stop)|(printf)|(skip)|(old)|(new)|(undefined)|(mux)|(validif)|(cmem)|(smem)|(mport)|(infer)|(read)|(write)|(rdwr)|(attach)|(assert)|(assume)|(cover)|(version)"
    )]
    Keyword,
    #[regex("[a-zA-Z_][a-zA-Z_0-9$]*", priority = 3)]
    Id,
    #[regex("[a-zA-Z_0-9$]+")]
    RelaxedId,
    #[regex(r"@\[\s*([^\]]*)\s*\]")]
    FileInfo,
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

        //let lexed = lexer().parse(modules[0]).unwrap();
        //println!("{:?}", lexed);
    }

    #[test]
    fn parse_token() {
        let lex = |s: &str| Token::lexer(s).map(|i| i.unwrap()).collect::<Vec<_>>();
        assert_eq!(lex("x1"), [Token::Id]);
        assert_eq!(lex("11"), [Token::RelaxedId]);
        assert_eq!(lex("@[test]"), [Token::FileInfo]);
        let mut lexer = Token::lexer("@[test]");
        lexer.next().unwrap().unwrap();
        assert_eq!(lexer.slice(), "test");
    }

    #[test]
    fn parse_expr() {}
}
