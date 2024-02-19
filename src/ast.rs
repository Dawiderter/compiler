use std::ops::Range;

use line_span::LineSpanExt;
use winnow::{
    combinator::{alt, delimited, opt, preceded, repeat, separated},
    error::{ContextError, ParseError},
    seq,
    token::one_of,
    PResult, Parser, Stateful,
};

use crate::lexer::{CondOperator, MathOperator, Token};

/// To AST w miarę dobrze oddaje gramatykę języka
/// program_all -> procedures main
/// procedures -> procedures PROCEDURE proc_head IS declarations IN commands END
/// | procedures PROCEDURE proc_head IS IN commands END
/// |
///
/// main -> PROGRAM IS declarations IN commands END
/// | PROGRAM IS IN commands END
///
/// commands -> commands command
/// | command
///
/// command -> identifier := expression ;
/// | IF condition THEN commands ELSE commands ENDIF
/// | IF condition THEN commands ENDIF
/// | WHILE condition DO commands ENDWHILE
/// | REPEAT commands UNTIL condition ;
/// | proc_call ;
/// | READ identifier ;
/// | WRITE value ;
///
/// proc_head -> pidentifier ( args_decl )
///
/// proc_call -> pidentifier ( args )
///
/// declarations -> declarations , pidentifier
/// | declarations , pidentifier [ num ]
/// | pidentifier
/// | pidentifier [ num ]
///
/// args_decl -> args_decl , pidentifier
/// | args_decl , T pidentifier
/// | pidentifier
/// | T pidentifier
///
/// args -> args , pidentifier
/// | pidentifier
///
/// expression -> value
/// | value + value
/// | value - value
/// | value * value
/// | value / value
/// | value % value
///
/// condition -> value = value
/// | value != value
/// | value > value
/// | value < value
/// | value >= value
/// | value <= value
///
/// value -> num
/// | identifier
///
/// identifier -> pidentifier
/// | pidentifier [ num ]
/// | pidentifier [ pidentifier ]

#[derive(Debug, Clone)]
pub struct ParsingError {
    pub body: String,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct ParsingState {
    pub errors: Vec<ParsingError>,
}

pub type TokenStream<'a> = Stateful<&'a [Token], ParsingState>;

/// identifier -> pidentifier
/// | pidentifier [ num ]
/// | pidentifier [ pidentifier ]
#[derive(Debug, Clone)]
pub enum Ident {
    Var(String),
    TabAccess(String, u64),
    IndirectTab(String, String),
}

/// value -> num
/// | identifier
#[derive(Debug, Clone)]
pub enum Value {
    Num(u64),
    Ident(Ident),
}

/// condition -> value = value
/// | value != value
/// | value > value
/// | value < value
/// | value >= value
/// | value <= value
#[derive(Debug, Clone)]
pub struct CondExpr {
    pub left: Value,
    pub right: Value,
    pub op: CondOperator,
}

/// binexpr -> value + value
/// | value - value
/// | value * value
/// | value / value
/// | value % value
#[derive(Debug, Clone)]
pub struct BinaryMathExpr {
    pub left: Value,
    pub right: Value,
    pub op: MathOperator,
}

/// expression -> value
/// | binexpr
#[derive(Debug, Clone)]
pub enum MathExpr {
    Value(Value),
    Binary(BinaryMathExpr),
}

/// args -> args , pidentifier
/// | pidentifier
#[derive(Debug, Clone)]
pub struct Args {
    pub list: Vec<String>,
}

/// arg_decl -> pidentifier
/// | T pidentifier
#[derive(Debug, Clone)]
pub enum ArgDecl {
    Var(String),
    Table(String),
}

/// args_decl -> args_decl , arg_decl
/// | arg_decl
#[derive(Debug, Clone)]
pub struct ArgDeclarations {
    pub list: Vec<ArgDecl>,
}

/// decl -> pidentifier
/// | pidentifier [ num ]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Var(String),
    Table(String, u64),
}

/// declarations -> declarations , decl
/// |
#[derive(Debug, Clone)]
pub struct Declarations {
    pub list: Vec<Decl>,
}

/// proc_call -> pidentifier ( args )
#[derive(Debug, Clone)]
pub struct ProcCall {
    pub pident: String,
    pub args: Args,
}

/// proc_head -> pidentifier ( args_decl )
#[derive(Debug, Clone)]
pub struct ProcHead {
    pub pident: String,
    pub args: ArgDeclarations,
}

/// command -> identifier := expression ;
/// | IF condition THEN commands ELSE commands ENDIF
/// | IF condition THEN commands ENDIF
/// | WHILE condition DO commands ENDWHILE
/// | REPEAT commands UNTIL condition ;
/// | proc_call ;
/// | READ identifier ;
/// | WRITE value ;
#[derive(Debug, Clone)]
pub enum Command {
    Assign(Ident, MathExpr),
    IfElse {
        cond: CondExpr,
        then: Commands,
        els: Commands,
    },
    If {
        cond: CondExpr,
        then: Commands,
    },
    While {
        cond: CondExpr,
        body: Commands,
    },
    Repeat {
        cond: CondExpr,
        body: Commands,
    },
    ProcCall(ProcCall),
    Inlined(Commands),
    Read(Ident),
    Write(Value),
}

/// commands -> commands command
/// | command
#[derive(Debug, Clone)]
pub struct Commands {
    pub list: Vec<Command>,
}

/// main -> PROGRAM IS declarations IN commands END
#[derive(Debug, Clone)]
pub struct Main {
    pub decls: Declarations,
    pub comms: Commands,
}

/// procedure -> PROCEDURE proc_head IS declarations IN commands END
#[derive(Debug, Clone)]
pub struct Procedure {
    pub head: ProcHead,
    pub decls: Declarations,
    pub comms: Commands,
}

/// procedures -> procedures procedure
/// |
#[derive(Debug, Clone)]
pub struct Procedures {
    pub list: Vec<Procedure>,
}

/// program_all -> procedures main
#[derive(Debug, Clone)]
pub struct Program {
    pub procs: Procedures,
    pub main: Main,
}

fn pident(i: &mut &[Token]) -> PResult<String> {
    one_of(|t| matches!(t, Token::PIdent(_)))
        .map(|t| match t {
            Token::PIdent(s) => s,
            _ => unreachable!(),
        })
        .parse_next(i)
}

/// identifier -> pidentifier
/// | pidentifier [ num ]
/// | pidentifier [ pidentifier ]
fn ident(i: &mut &[Token]) -> PResult<Ident> {
    (
        one_of(|t| matches!(t, Token::PIdent(_))),
        opt(delimited(
            one_of(Token::OpenBrace),
            one_of(|t| matches!(t, Token::PIdent(_)) || matches!(t, Token::Num(_))),
            one_of(Token::CloseBrace),
        )),
    )
        .map(|res| match res {
            (Token::PIdent(a), None) => Ident::Var(a),
            (Token::PIdent(a), Some(Token::Num(b))) => Ident::TabAccess(a, b),
            (Token::PIdent(a), Some(Token::PIdent(b))) => Ident::IndirectTab(a, b),
            _ => unreachable!(),
        })
        .parse_next(i)
}

/// value -> num
/// | identifier
fn value(i: &mut &[Token]) -> PResult<Value> {
    alt((
        one_of(|t| matches!(t, Token::Num(_))).map(|t| match t {
            Token::Num(v) => Value::Num(v),
            _ => unreachable!(),
        }),
        ident.map(Value::Ident),
    ))
    .parse_next(i)
}

/// condition -> value = value
/// | value != value
/// | value > value
/// | value < value
/// | value >= value
/// | value <= value
fn condexpr(i: &mut &[Token]) -> PResult<CondExpr> {
    (
        value,
        one_of(|t| matches!(t, Token::CondOperator(_))).map(|t| match t {
            Token::CondOperator(op) => op,
            _ => unreachable!(),
        }),
        value,
    )
        .map(|(left, op, right)| CondExpr { left, op, right })
        .parse_next(i)
}

/// binexpr -> value + value
/// | value - value
/// | value * value
/// | value / value
/// | value % value
fn binary_mathexpr(i: &mut &[Token]) -> PResult<BinaryMathExpr> {
    (
        value,
        one_of(|t| matches!(t, Token::MathOperator(_))).map(|t| match t {
            Token::MathOperator(op) => op,
            _ => unreachable!(),
        }),
        value,
    )
        .map(|(left, op, right)| BinaryMathExpr { left, op, right })
        .parse_next(i)
}

/// expression -> value
/// | binexpr
fn mathexpr(i: &mut &[Token]) -> PResult<MathExpr> {
    alt((
        binary_mathexpr.map(MathExpr::Binary),
        value.map(MathExpr::Value),
    ))
    .parse_next(i)
}

/// args -> args , pidentifier
/// | pidentifier
fn args(i: &mut &[Token]) -> PResult<Args> {
    separated(1.., pident, one_of(Token::Comma))
        .map(|list| Args { list })
        .parse_next(i)
}

/// arg_decl -> pidentifier
/// | T pidentifier
fn argdecl(i: &mut &[Token]) -> PResult<ArgDecl> {
    alt((
        preceded(one_of(Token::T), pident).map(ArgDecl::Table),
        pident.map(ArgDecl::Var),
    ))
    .parse_next(i)
}

/// args_decl -> args_decl , arg_decl
/// | arg_decl
fn argdecls(i: &mut &[Token]) -> PResult<ArgDeclarations> {
    separated(1.., argdecl, one_of(Token::Comma))
        .map(|list| ArgDeclarations { list })
        .parse_next(i)
}

/// decl -> pidentifier
/// | pidentifier [ num ]
fn decl(i: &mut &[Token]) -> PResult<Decl> {
    (
        one_of(|t| matches!(t, Token::PIdent(_))),
        opt(delimited(
            one_of(Token::OpenBrace),
            one_of(|t| matches!(t, Token::Num(_))),
            one_of(Token::CloseBrace),
        )),
    )
        .map(|res| match res {
            (Token::PIdent(a), None) => Decl::Var(a),
            (Token::PIdent(a), Some(Token::Num(b))) => Decl::Table(a, b),
            _ => unreachable!(),
        })
        .parse_next(i)
}

/// declarations -> declarations , decl
/// |
fn decls(i: &mut &[Token]) -> PResult<Declarations> {
    separated(0.., decl, one_of(Token::Comma))
        .map(|list| Declarations { list })
        .parse_next(i)
}

/// proc_call -> pidentifier ( args )
fn proc_call(i: &mut &[Token]) -> PResult<ProcCall> {
    (
        pident,
        delimited(one_of(Token::OpenParen), args, one_of(Token::CloseParen)),
    )
        .map(|(pident, args)| ProcCall { pident, args })
        .parse_next(i)
}

/// proc_head -> pidentifier ( args_decl )
fn proc_head(i: &mut &[Token]) -> PResult<ProcHead> {
    (
        pident,
        delimited(
            one_of(Token::OpenParen),
            argdecls,
            one_of(Token::CloseParen),
        ),
    )
        .map(|(pident, args)| ProcHead { pident, args })
        .parse_next(i)
}

/// command -> identifier := expression ;
/// | IF condition THEN commands ELSE commands ENDIF
/// | IF condition THEN commands ENDIF
/// | WHILE condition DO commands ENDWHILE
/// | REPEAT commands UNTIL condition ;
/// | proc_call ;
/// | READ identifier ;
/// | WRITE value ;
fn command(i: &mut &[Token]) -> PResult<Command> {
    alt((
        seq!(
            _: one_of(Token::If), condexpr, _: one_of(Token::Then), commands, _: one_of(Token::Endif)
        ).map(|(cond,then)| Command::If { cond, then }),
        seq!(
            _: one_of(Token::If), condexpr, _: one_of(Token::Then), commands, _: one_of(Token::Else), commands, _: one_of(Token::Endif)
        ).map(|(cond,then, els)| Command::IfElse { cond, then, els }),
        seq!(
            _: one_of(Token::While), condexpr, _: one_of(Token::Do), commands, _: one_of(Token::Endwhile)
        ).map(|(cond,body)| Command::While { cond, body }),
        seq!(
            _: one_of(Token::Repeat), commands, _: one_of(Token::Until), condexpr, _: one_of(Token::SemiColon)
        ).map(|(body,cond)| Command::Repeat { cond, body }),
        seq!(
            _: one_of(Token::Read), ident, _: one_of(Token::SemiColon)
        ).map(|(i,)| Command::Read(i)),
        seq!(
            _: one_of(Token::Write), value, _: one_of(Token::SemiColon)
        ).map(|(v,)| Command::Write(v)),
        seq!(
            ident, _: one_of(Token::Assign), mathexpr, _: one_of(Token::SemiColon)
        ).map(|(i,e)| Command::Assign(i, e)),
        seq!(
            proc_call, _: one_of(Token::SemiColon)
        ).map(|(c,)| Command::ProcCall(c)),
    ))
    .parse_next(i)
}

/// commands -> commands command
/// | command
fn commands(i: &mut &[Token]) -> PResult<Commands> {
    repeat(1.., command)
        .map(|list| Commands { list })
        .parse_next(i)
}

/// main -> PROGRAM IS declarations IN commands END
pub fn main(i: &mut &[Token]) -> PResult<Main> {
    seq!(_: one_of(Token::Program), _: one_of(Token::Is), decls, _:one_of(Token::In), commands, _:one_of(Token::End))
    .map(|(decls,comms)| Main { decls, comms }).parse_next(i)
}

/// procedure -> PROCEDURE proc_head IS declarations IN commands END
pub fn procedure(i: &mut &[Token]) -> PResult<Procedure> {
    seq!(_: one_of(Token::Procedure), proc_head, _: one_of(Token::Is), decls, _:one_of(Token::In), commands, _:one_of(Token::End))
    .map(|(head, decls,comms)| Procedure { head, decls, comms }).parse_next(i)
}

/// procedures -> procedures procedure
/// |
pub fn procedures(i: &mut &[Token]) -> PResult<Procedures> {
    repeat(0.., procedure)
        .map(|list| Procedures { list })
        .parse_next(i)
}

/// program_all -> procedures main
pub fn program(i: &mut &[Token]) -> PResult<Program> {
    (procedures, main)
        .map(|(procs, main)| Program { procs, main })
        .parse_next(i)
}

pub fn ok_with_report(
    input: &str,
    token_spans: &[Range<usize>],
    result: Result<Program, ParseError<&[Token], ContextError>>,
) -> Option<Program> {
    use owo_colors::OwoColorize;

    match result {
        Ok(p) => Some(p),
        Err(e) => {
            let offset = e.offset();
            let span = &token_spans[offset];

            for (line_number, lin) in input.line_spans().enumerate() {
                if lin.range().contains(&span.start) {
                    println!(
                        "On line {} parsing error near: {}{}{}",
                        line_number.bold(),
                        &input[lin.start()..span.start],
                        (&input[span.start..span.end]).bold().red(),
                        &input[span.end..lin.end()]
                    );

                    break;
                }
            }

            None
        }
    }
}
