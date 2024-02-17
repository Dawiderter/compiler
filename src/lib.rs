use ast::{ok_with_report, program};
use ast_analysis::optimize_ast;
use lexer::report_lex_errors;
use machine::MachProgramBuilder;
use mir::MirBuilder;
use mir_analysis::{flatten, optimize_mir};
use winnow::Parser;

use crate::lexer::lex_str;

pub mod ast;
pub mod ast_analysis;
pub mod lexer;
pub mod machine;
pub mod mir;
pub mod mir_analysis;

pub fn build_code(input: &str) -> Result<MachProgramBuilder, ()> {
    let lex = lex_str(input);

    if !lex.errors.is_empty() {
        report_lex_errors(input, &lex.errors);
        return Err(());
    }

    let prog = program.parse(&lex.tokens);

    let Ok(mut prog) = prog else {
        ok_with_report(input, &lex.spans, prog);
        return Err(());
    };

    if !optimize_ast(&mut prog) {
        return Err(());
    }

    let builder = MirBuilder::build_program(&prog);

    let opt_res = optimize_mir(&builder);
    let instr = flatten(&builder);

    let mut mach = MachProgramBuilder {
        variables: builder.variables,
        spills: opt_res.already_set,
        memory: opt_res.memory,
        labels: builder.labels,
        ..Default::default()
    };

    mach.build(&instr);

    Ok(mach)
}
