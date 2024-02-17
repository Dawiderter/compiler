use std::{collections::HashMap, fmt::Display};

use slotmap::{new_key_type, Key, SlotMap};
use smallvec::{smallvec, SmallVec};

use crate::{
    ast::{self, Main, Procedure, Program},
    ast_analysis,
};

new_key_type! { pub struct MirVar; }
new_key_type! { pub struct MirProcedure; }
new_key_type! { pub struct MirLabel; }

pub trait Id {
    fn id(&self) -> u64;
}

impl<T: Key> Id for T {
    fn id(&self) -> u64 {
        self.data().as_ffi() & (!0 >> 32)
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub enum MirVarType {
    #[default]
    Local,
    Arg,
    TableLocal(u64),
    TableArg,
}

#[derive(Debug, Clone, Copy, Default)]
pub enum MirVarInitStatus {
    UnconditionalInit,
    MaybeInit,
    #[default]
    NotInit,
}

/// Unused for now
#[derive(Debug, Clone, Default)]
pub struct MirVarInfo {
    pub typ: MirVarType,
    pub uses: u32,
    pub loop_uses: u32,
    pub max_loop_depth: u32,
}

#[derive(Debug, Clone, Copy)]
pub enum MirValue {
    Var(MirVar),
    Const(u64),
}

#[derive(Debug, Clone, Copy)]
pub enum MathOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Debug, Clone, Copy)]
pub enum CondOp {
    IsEqual,
    IsNotEqual,
    IsLess,
    IsLessEqual,
}

#[derive(Debug, Clone, Copy)]
pub enum MirInstr {
    /// Wrzuć do 0 to co jest pod adresem wskazywanym przez 1
    Load(MirVar, MirVar),
    /// Wrzuć do adresu wskazywanego przez 0 to co jest pod 1
    Store(MirVar, MirValue),
    /// Wrzuć do 0 to co jest pod 1
    Assign(MirVar, MirValue),
    /// Wrzuć do 0 wynik działania 1 ( + | - | * | / ) 2
    AssignExpr(MirVar, MirValue, MathOp, MirValue),
    /// Wrzuć do 0 adres zmiennej pod 1
    LoadAddress(MirVar, MirVar),
    /// Przejdź do instrukcji 0, jeśli ustawione jest 1 to skok następuje do innej procedury
    Jump(MirLabel, Option<MirProcedure>),
    /// Przejdź do instrukcji 0 sprawdzając czy spełnione jest 1 ( < | = ) 2
    JumpCond(MirLabel, MirValue, CondOp, MirValue),
    // Zapisz miejsce obecnej instrukcji w 0
    Strk(MirVar),
    // Przejdź do instrukcji na którą wskazuje 0
    JumpReturn(MirVar),
    /// Czytaj do zmiennej 0
    Read(MirVar),
    // Wypisz wartość 1
    Write(MirValue),
    // Pozycja labela 0
    Label(MirLabel),
    // Koniec programu
    Halt,
    // Noop
    Noop,
    // Noop, który jest traktowany jako odczytanie 0
    NoopRead(MirVar),
}

impl MirInstr {
    pub fn is_terminator(&self) -> bool {
        matches!(
            self,
            MirInstr::Jump(_, None)
                | MirInstr::JumpCond(_, _, _, _)
                | MirInstr::JumpReturn(_)
                | MirInstr::Halt
        )
    }

    pub fn uses(&self) -> SmallVec<[MirVar; 2]> {
        match self {
            MirInstr::Assign(_, val) | MirInstr::Write(val) => {
                if let MirValue::Var(var) = val {
                    smallvec![*var]
                } else {
                    smallvec![]
                }
            }
            MirInstr::Store(var, val) => {
                if let MirValue::Var(var_val) = val {
                    smallvec![*var_val, *var]
                } else {
                    smallvec![*var]
                }
            }
            MirInstr::AssignExpr(_, val_a, _, val_b) | MirInstr::JumpCond(_, val_a, _, val_b) => {
                match (val_a, val_b) {
                    (MirValue::Var(var_a), MirValue::Var(var_b)) => smallvec![*var_a, *var_b],
                    (MirValue::Var(var), _) => smallvec![*var],
                    (_, MirValue::Var(var)) => smallvec![*var],
                    _ => smallvec![],
                }
            }
            MirInstr::NoopRead(var) | MirInstr::JumpReturn(var) | MirInstr::LoadAddress(_, var) | MirInstr::Load(_, var) => {
                smallvec![*var]
            }
            _ => smallvec![],
        }
    }

    pub fn defs(&self) -> Option<MirVar> {
        match self {
            MirInstr::Assign(var, _)
            | MirInstr::AssignExpr(var, _, _, _)
            | MirInstr::LoadAddress(var, _)
            | MirInstr::Load(var, _)
            | MirInstr::Strk(var)
            | MirInstr::Read(var) => Some(*var),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct MirProcedureInfo {
    pub args: Vec<MirVar>,
    pub return_var: MirVar,
    pub start: MirLabel,
    pub instr: Vec<MirInstr>,
}

#[derive(Debug, Clone, Default)]
pub struct MirBuilder {
    pub variables: SlotMap<MirVar, MirVarInfo>,
    pub var_names: HashMap<String, MirVar>,
    pub procedures: SlotMap<MirProcedure, MirProcedureInfo>,
    pub proc_names: HashMap<String, MirProcedure>,
    pub main: MirProcedure,
    pub labels: SlotMap<MirLabel, ()>,
    // prev_var_info: HashMap<String, ast_analysis::VarInfo>,
}

impl MirBuilder {
    pub fn build_program(
        prog: &Program,
        // prev_var_info: HashMap<String, ast_analysis::VarInfo>,
    ) -> Self {
        let mut builder = MirBuilder {
            // prev_var_info,
            ..Default::default()
        };

        for proc in &prog.procs.list {
            builder.build_procedure(proc);
        }

        builder.build_main(&prog.main);

        builder
    }

    fn add_named_var(&mut self, name: &str, info: MirVarInfo) -> MirVar {
        let id = self.variables.insert(info);
        self.var_names.insert(name.to_owned(), id);
        id
    }

    fn new_var(&mut self) -> MirVar {
        self.variables.insert(MirVarInfo::default())
    }

    fn new_label(&mut self) -> MirLabel {
        self.labels.insert(())
    }

    fn build_procedure(&mut self, proc: &Procedure) {
        let Procedure { head, decls, comms } = proc;
        let mut info = MirProcedureInfo::default();

        for arg in &head.args.list {
            let id = match arg {
                ast::ArgDecl::Var(name) => self.add_named_var(
                    name,
                    MirVarInfo {
                        typ: MirVarType::Arg,
                        ..Default::default()
                    },
                ),
                ast::ArgDecl::Table(name) => self.add_named_var(
                    name,
                    MirVarInfo {
                        typ: MirVarType::TableArg,
                        ..Default::default()
                    },
                ),
            };
            info.args.push(id);
        }

        for decl in &decls.list {
            match decl {
                ast::Decl::Var(name) => {
                    self.add_named_var(
                        name,
                        MirVarInfo {
                            typ: MirVarType::Local,
                            ..Default::default()
                        },
                    );
                }
                ast::Decl::Table(name, n) => {
                    self.add_named_var(
                        name,
                        MirVarInfo {
                            typ: MirVarType::TableLocal(*n),
                            ..Default::default()
                        },
                    );
                }
            }
        }

        info.return_var = self.new_var();
        info.start = self.new_label();

        let mut instr = vec![MirInstr::Label(info.start)];

        self.build_commands(comms, &mut instr);

        instr.push(MirInstr::JumpReturn(info.return_var));

        info.instr = instr;

        let id = self.procedures.insert(info);
        self.proc_names.insert(head.pident.to_owned(), id);
    }

    fn build_main(&mut self, main: &Main) {
        let Main { decls, comms } = main;

        for decl in &decls.list {
            match decl {
                ast::Decl::Var(name) => {
                    self.add_named_var(
                        name,
                        MirVarInfo {
                            typ: MirVarType::Local,
                            ..Default::default()
                        },
                    );
                }
                ast::Decl::Table(name, n) => {
                    self.add_named_var(
                        name,
                        MirVarInfo {
                            typ: MirVarType::TableLocal(*n),
                            ..Default::default()
                        },
                    );
                }
            }
        }

        let mut instr = vec![];
        self.build_commands(comms, &mut instr);
        instr.push(MirInstr::Halt);

        let id = self.procedures.insert(MirProcedureInfo {
            instr,
            ..Default::default()
        });
        self.main = id;
    }

    fn build_commands(&mut self, commands: &ast::Commands, instr_buffer: &mut Vec<MirInstr>) {
        for command in &commands.list {
            self.build_command(command, instr_buffer);
        }
    }

    fn build_command(&mut self, command: &ast::Command, instr_buffer: &mut Vec<MirInstr>) {
        match command {
            ast::Command::Assign(left, right) => {
                self.build_assign(instr_buffer, left, right);
            }
            ast::Command::IfElse { cond, then, els } => {
                self.build_if_else(instr_buffer, cond, then, els);
            }
            ast::Command::If { cond, then } => {
                self.build_if(instr_buffer, cond, then);
            }
            ast::Command::While { cond, body } => {
                self.build_while(instr_buffer, cond, body);
            }
            ast::Command::Repeat { cond, body } => {
                self.build_repeat(instr_buffer, cond, body);
            }
            ast::Command::ProcCall(proc) => {
                self.build_proc_call(instr_buffer, proc);
            }
            ast::Command::Inlined(body) => {
                self.build_commands(body, instr_buffer);
            }
            ast::Command::Read(ident) => {
                self.build_read(instr_buffer, ident);
            }
            ast::Command::Write(val) => {
                self.build_write(instr_buffer, val);
            }
        }
    }

    /// Zwraca wartość, którą można znaleźć pod val
    fn value_to_mir(&mut self, instr_buffer: &mut Vec<MirInstr>, val: &ast::Value) -> MirValue {
        match val {
            ast::Value::Num(n) => MirValue::Const(*n),
            ast::Value::Ident(i) => MirValue::Var(self.ident_to_mir(instr_buffer, i)),
        }
    }

    /// Zwraca zmienną, w której można znaleźć wartość zmiennej pod ident
    fn ident_to_mir(&mut self, instr_buffer: &mut Vec<MirInstr>, ident: &ast::Ident) -> MirVar {
        match ident {
            ast::Ident::Var(name) => self.pident_to_mir(instr_buffer, name),
            ast::Ident::TabAccess(name, n) => {
                let start = self.pident_to_mir(instr_buffer, name);
                instr_buffer.push(MirInstr::AssignExpr(
                    start,
                    MirValue::Var(start),
                    MathOp::Add,
                    MirValue::Const(*n),
                ));
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::Load(new_var, start));
                new_var
            }
            ast::Ident::IndirectTab(name, index) => {
                let index = self.pident_to_mir(instr_buffer, index);
                let start = self.pident_to_mir(instr_buffer, name);
                instr_buffer.push(MirInstr::AssignExpr(
                    start,
                    MirValue::Var(start),
                    MathOp::Add,
                    MirValue::Var(index),
                ));
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::Load(new_var, start));
                new_var
            }
        }
    }

    /// Zwraca zmienną, w której można znaleźć wartość zmiennej pod pident
    /// Lub początek tablicy, gdy jest to tablica
    fn pident_to_mir(&mut self, instr_buffer: &mut Vec<MirInstr>, pident: &str) -> MirVar {
        let var = self.var_names[pident];
        let info = &self.variables[var];
        match info.typ {
            MirVarType::Local => var,
            MirVarType::Arg => {
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::Load(new_var, var));
                new_var
            }
            MirVarType::TableLocal(_) => {
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::LoadAddress(new_var, var));
                new_var
            }
            MirVarType::TableArg => {
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::Assign(new_var, MirValue::Var(var)));
                new_var
            }
        }
    }

    fn build_assign(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        top_left: &ast::Ident,
        right: &ast::MathExpr,
    ) {
        match right {
            ast::MathExpr::Value(val) => {
                let right = self.value_to_mir(instr_buffer, val);
                self.build_single_assign(instr_buffer, top_left, right);
            }
            ast::MathExpr::Binary(ast::BinaryMathExpr { left, right, op }) => {
                let op = match op {
                    crate::lexer::MathOperator::Add => MathOp::Add,
                    crate::lexer::MathOperator::Sub => MathOp::Sub,
                    crate::lexer::MathOperator::Mul => MathOp::Mul,
                    crate::lexer::MathOperator::Div => MathOp::Div,
                    crate::lexer::MathOperator::Rem => MathOp::Rem,
                };
                let right_a = self.value_to_mir(instr_buffer, left);
                let right_b = self.value_to_mir(instr_buffer, right);
                self.build_binary_assign(instr_buffer, top_left, right_a, right_b, op);
            }
        }
    }

    fn build_single_assign(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        left: &ast::Ident,
        right: MirValue,
    ) {
        match left {
            ast::Ident::Var(a) => {
                let var = self.var_names[a];
                let info = &self.variables[var];
                match info.typ {
                    MirVarType::Local => {
                        instr_buffer.push(MirInstr::Assign(var, right));
                    }
                    MirVarType::Arg => {
                        instr_buffer.push(MirInstr::Store(var, right));
                    }
                    _ => {}
                }
            }
            ast::Ident::TabAccess(name, n) => {
                let start = self.pident_to_mir(instr_buffer, name);
                instr_buffer.push(MirInstr::AssignExpr(
                    start,
                    MirValue::Var(start),
                    MathOp::Add,
                    MirValue::Const(*n),
                ));
                instr_buffer.push(MirInstr::Store(start, right));
            }
            ast::Ident::IndirectTab(name, index) => {
                let index = self.pident_to_mir(instr_buffer, index);
                let start = self.pident_to_mir(instr_buffer, name);
                instr_buffer.push(MirInstr::AssignExpr(
                    start,
                    MirValue::Var(start),
                    MathOp::Add,
                    MirValue::Var(index),
                ));
                instr_buffer.push(MirInstr::Store(start, right));
            }
        }
    }

    fn build_binary_assign(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        left: &ast::Ident,
        right_a: MirValue,
        right_b: MirValue,
        op: MathOp,
    ) {
        match left {
            ast::Ident::Var(a) => {
                let var = self.var_names[a];
                let info = &self.variables[var];
                match info.typ {
                    MirVarType::Local => {
                        instr_buffer.push(MirInstr::AssignExpr(var, right_a, op, right_b));
                    }
                    MirVarType::Arg => {
                        let new_var = self.new_var();
                        instr_buffer.push(MirInstr::AssignExpr(new_var, right_a, op, right_b));
                        self.build_single_assign(instr_buffer, left, MirValue::Var(new_var));
                    }
                    _ => {}
                }
            }
            _ => {
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::AssignExpr(new_var, right_a, op, right_b));
                self.build_single_assign(instr_buffer, left, MirValue::Var(new_var));
            }
        }
    }

    fn build_on_true_jump(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        cond: &ast::CondExpr,
        jump_to: MirLabel,
    ) {
        let ast::CondExpr { left, right, op } = cond;
        let left = self.value_to_mir(instr_buffer, left);
        let right = self.value_to_mir(instr_buffer, right);
        match op {
            crate::lexer::CondOperator::Equal => {
                instr_buffer.push(MirInstr::JumpCond(jump_to, left, CondOp::IsEqual, right));
            }
            crate::lexer::CondOperator::NotEqual => {
                instr_buffer.push(MirInstr::JumpCond(jump_to, left, CondOp::IsNotEqual, right));
            }
            crate::lexer::CondOperator::Greater => {
                instr_buffer.push(MirInstr::JumpCond(jump_to, right, CondOp::IsLess, left));
            }
            crate::lexer::CondOperator::Lesser => {
                instr_buffer.push(MirInstr::JumpCond(jump_to, left, CondOp::IsLess, right));
            }
            crate::lexer::CondOperator::GreaterEq => {
                instr_buffer.push(MirInstr::JumpCond(
                    jump_to,
                    right,
                    CondOp::IsLessEqual,
                    left,
                ));
            }
            crate::lexer::CondOperator::LesserEq => {
                instr_buffer.push(MirInstr::JumpCond(
                    jump_to,
                    left,
                    CondOp::IsLessEqual,
                    right,
                ));
            }
        }
    }

    fn build_on_false_jump(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        cond: &ast::CondExpr,
        jump_to: MirLabel,
    ) {
        let ast::CondExpr { left, right, op } = cond;
        let inv_op = match op {
            crate::lexer::CondOperator::Equal => crate::lexer::CondOperator::NotEqual,
            crate::lexer::CondOperator::NotEqual => crate::lexer::CondOperator::Equal,
            crate::lexer::CondOperator::Greater => crate::lexer::CondOperator::LesserEq,
            crate::lexer::CondOperator::Lesser => crate::lexer::CondOperator::GreaterEq,
            crate::lexer::CondOperator::GreaterEq => crate::lexer::CondOperator::Lesser,
            crate::lexer::CondOperator::LesserEq => crate::lexer::CondOperator::Greater,
        };

        self.build_on_true_jump(
            instr_buffer,
            &ast::CondExpr {
                left: left.clone(),
                right: right.clone(),
                op: inv_op,
            },
            jump_to,
        );
    }

    fn build_if(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        cond: &ast::CondExpr,
        then: &ast::Commands,
    ) {
        let label = self.new_label();
        self.build_on_false_jump(instr_buffer, cond, label);

        self.build_commands(then, instr_buffer);
        instr_buffer.push(MirInstr::Label(label));
    }

    fn build_if_else(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        cond: &ast::CondExpr,
        then: &ast::Commands,
        els: &ast::Commands,
    ) {
        let label = self.new_label();
        let end = self.new_label();
        self.build_on_false_jump(instr_buffer, cond, label);

        self.build_commands(then, instr_buffer);
        instr_buffer.push(MirInstr::Jump(end, None));
        instr_buffer.push(MirInstr::Label(label));
        self.build_commands(els, instr_buffer);
        instr_buffer.push(MirInstr::Label(end));
    }

    fn build_while(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        cond: &ast::CondExpr,
        body: &ast::Commands,
    ) {
        let start = self.new_label();
        let label = self.new_label();

        instr_buffer.push(MirInstr::Label(start));

        self.build_on_false_jump(instr_buffer, cond, label);

        self.build_commands(body, instr_buffer);
        instr_buffer.push(MirInstr::Jump(start, None));
        instr_buffer.push(MirInstr::Label(label));
    }

    fn build_repeat(
        &mut self,
        instr_buffer: &mut Vec<MirInstr>,
        cond: &ast::CondExpr,
        body: &ast::Commands,
    ) {
        let start = self.new_label();

        instr_buffer.push(MirInstr::Label(start));

        self.build_commands(body, instr_buffer);

        self.build_on_false_jump(instr_buffer, cond, start);
    }

    fn build_proc_call(&mut self, instr_buffer: &mut Vec<MirInstr>, proc: &ast::ProcCall) {
        let ast::ProcCall { pident, args } = proc;
        let proc_id = self.proc_names[pident];
        let proc = &self.procedures[proc_id];

        for (arg, &calee_arg) in args.list.iter().zip(proc.args.iter()) {
            let var = self.var_names[arg];
            let var_info = &self.variables[var];

            match var_info.typ {
                MirVarType::Local | MirVarType::TableLocal(_) => {
                    instr_buffer.push(MirInstr::LoadAddress(calee_arg, var));
                }
                MirVarType::Arg | MirVarType::TableArg => {
                    instr_buffer.push(MirInstr::Assign(calee_arg, MirValue::Var(var)));
                }
            }
        }

        instr_buffer.push(MirInstr::Strk(proc.return_var));
        instr_buffer.push(MirInstr::Jump(proc.start, Some(proc_id)));

        instr_buffer.push(MirInstr::NoopRead(proc.return_var));
        for &calee_arg in proc.args.iter().rev() {
            instr_buffer.push(MirInstr::NoopRead(calee_arg));
        }
        
    }

    fn build_read(&mut self, instr_buffer: &mut Vec<MirInstr>, ident: &ast::Ident) {
        match ident {
            ast::Ident::Var(a) => {
                let var = self.var_names[a];
                let info = &self.variables[var];
                match info.typ {
                    MirVarType::Local => {
                        instr_buffer.push(MirInstr::Read(var));
                    }
                    MirVarType::Arg => {
                        let new_var = self.new_var();
                        instr_buffer.push(MirInstr::Read(new_var));
                        instr_buffer.push(MirInstr::Store(var, MirValue::Var(new_var)));
                    }
                    _ => {}
                }
            }
            ast::Ident::TabAccess(name, n) => {
                let start = self.pident_to_mir(instr_buffer, name);
                instr_buffer.push(MirInstr::AssignExpr(
                    start,
                    MirValue::Var(start),
                    MathOp::Add,
                    MirValue::Const(*n),
                ));
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::Read(new_var));
                instr_buffer.push(MirInstr::Store(start, MirValue::Var(new_var)));
            }
            ast::Ident::IndirectTab(name, index) => {
                let index = self.pident_to_mir(instr_buffer, index);
                let start = self.pident_to_mir(instr_buffer, name);
                instr_buffer.push(MirInstr::AssignExpr(
                    start,
                    MirValue::Var(start),
                    MathOp::Add,
                    MirValue::Var(index),
                ));
                let new_var = self.new_var();
                instr_buffer.push(MirInstr::Read(new_var));
                instr_buffer.push(MirInstr::Store(start, MirValue::Var(new_var)));
            }
        }
    }

    fn build_write(&mut self, instr_buffer: &mut Vec<MirInstr>, val: &ast::Value) {
        let val = self.value_to_mir(instr_buffer, val);
        instr_buffer.push(MirInstr::Write(val));
    }
}

impl Display for MirVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.id())
    }
}

impl Display for MirValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirValue::Var(var) => write!(f, "{}", var),
            MirValue::Const(n) => write!(f, "{}", n),
        }
    }
}

impl Display for MirLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.id())
    }
}

impl Display for MathOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MathOp::Add => write!(f, "+"),
            MathOp::Sub => write!(f, "-"),
            MathOp::Mul => write!(f, "*"),
            MathOp::Div => write!(f, "/"),
            MathOp::Rem => write!(f, "%"),
        }
    }
}

impl Display for CondOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CondOp::IsEqual => write!(f, "="),
            CondOp::IsLess => write!(f, "<"),
            CondOp::IsNotEqual => write!(f, "!="),
            CondOp::IsLessEqual => write!(f, "<="),
        }
    }
}

impl Display for MirInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirInstr::Load(var, addr) => {
                write!(f, "load {} [{}]", var, addr)
            }
            MirInstr::Store(addr, val) => {
                write!(f, "store [{}] {}", addr, val)
            }
            MirInstr::Assign(var, val) => {
                write!(f, "{} := {}", var, val)
            }
            MirInstr::AssignExpr(var, val_a, op, val_b) => {
                write!(f, "{} := {} {} {}", var, val_a, op, val_b)
            }
            MirInstr::LoadAddress(var_a, var_b) => {
                write!(f, "{} := &{}", var_a, var_b)
            }
            MirInstr::Jump(label, to_proc) => {
                write!(f, "jump {} (proc: {:?})", label, to_proc)
            }
            MirInstr::JumpCond(label, val_a, op, val_b) => {
                write!(f, "jump {} if {} {} {}", label, val_a, op, val_b)
            }
            MirInstr::Strk(var) => {
                write!(f, "strk {}", var)
            }
            MirInstr::JumpReturn(var) => {
                write!(f, "jump return {}", var)
            }
            MirInstr::Read(var) => {
                write!(f, "read {}", var)
            }
            MirInstr::Write(val) => {
                write!(f, "write {}", val)
            }
            MirInstr::Label(label) => {
                write!(f, "{}:", label)
            }
            MirInstr::Halt => write!(f, "halt"),
            MirInstr::Noop => write!(f, "noop"),
            MirInstr::NoopRead(var) => write!(f, "noop {}", var),
        }
    }
}

impl Display for MirBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (proc_id, proc) in &self.procedures {
            write!(f, "fn@{} ", proc_id.id())?;
            write!(f, "ret: {} ", proc.return_var)?;
            write!(f, "args: ")?;
            for arg in &proc.args {
                write!(f, "{} ", arg)?;
            }
            writeln!(f)?;
            for instr in &proc.instr {
                writeln!(f, "   {}", instr)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use winnow::Parser;

    use crate::{ast::program, ast_analysis::optimize_ast, lexer::lex_str};

    use super::*;

    fn gen_prog() -> Program {
        let test = r"
        PROCEDURE shuffle(T t, n) IS
        i, q, w
      IN
        q:=5;
        w:=1;
        i:=0;
        WHILE i<n DO
          w:=w*q;
          w:=w%n;
          t[i]:=w;
          i:=i+1;
        ENDWHILE
        i:=n-1;
        t[i]:=0;
      END
      
      PROCEDURE sort(T t, n) IS
        x, i, j, k
      IN
        i:=1;
        WHILE i<n DO
          x:=t[i];
          j:=i;
          WHILE j>0 DO
            k:=j-1;
            IF t[k]>x THEN
              t[j]:=t[k];
              j:=j-1;
            ELSE
              k:=j;
              j:=0;
            ENDIF
          ENDWHILE
          t[k]:=x;
          i:=i+1;
        ENDWHILE
      END
      
      PROCEDURE write(T t, n) IS
        i
      IN
        i:=0;
        WHILE i<n DO
          WRITE t[i];
          i:=i+1;
        ENDWHILE
      END
      
      PROGRAM IS
        t[23], n
      IN
        n:=23;
        shuffle(t,n);
        write(t,n);
        WRITE 1234567890;
        sort(t,n);
        write(t,n);
      END
        ";

        let lex = lex_str(test);
        assert!(lex.errors.is_empty());
        let mut prog = program.parse(&lex.tokens).unwrap();
        optimize_ast(&mut prog);
        prog
    }

    #[test]
    fn generation_test() {
        let prog = gen_prog();
        let builder = MirBuilder::build_program(&prog);

        eprintln!("{}", builder);
    }
}
