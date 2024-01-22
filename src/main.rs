use std::{fs::read_to_string, env::args};

use compiler_basic::{
    ast::{program, ok_with_report},
    lexer::{lex_str, report_lex_errors},
    machine::MachProgram,
    triaddress::IRProgram,
};
use winnow::Parser;

fn main() {
    let input_path = args().nth(1).expect("Input path missing");
    let input = read_to_string(input_path).unwrap();
    let tokens = lex_str(&input);
    report_lex_errors(&input, &tokens.errors);
    assert!(tokens.errors.is_empty());
    let prog = program.parse(&tokens.tokens);
    let prog = ok_with_report(&input, &tokens.spans, prog).unwrap();
    let ir_prog = IRProgram::generate(prog).unwrap();
    println!("{}", ir_prog);
    let mach = MachProgram::generate(ir_prog);
    //println!("{}", mach);
}
