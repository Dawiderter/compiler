use std::collections::HashMap;

use crate::ast::{self, Command, Commands, Ident, Program};

#[derive(Debug, Clone, Copy, Default)]
pub struct ProcInfo {
    uses: u32,
    approx_length: u32,
    visited: bool,
}

/// Sprawdzanie użycia procedur:
/// - czy nie została użyta nieznana procedura
/// - czy nie została użyta przed swoją definicją
/// - czy nie ma kolizji nazw procedur
/// Dodatkowo zbieranie informacji:
/// - która procedura została w ogóle użyta (idąc od maina) i ile razy
/// - jak dużo linijek ma dana procedura 
#[derive(Debug, Clone, Default)]
pub struct ProcUseChecker {
    used_walk_stack: Vec<usize>,
    info: Vec<ProcInfo>,
    curr_proc: Option<usize>,
    names: HashMap<String, usize>,
    errors: Vec<ProcUseErr>,
}

#[derive(Debug, Clone)]
pub enum ProcUseErr {
    ProcUseBeforeDeclaration(String),
    UnknownProc(String),
    ProcNameCollision(String),
}

impl ProcUseChecker {
    pub fn check_prog(program: &Program) -> ProcUseChecker {
        let mut checker = Self::default();

        for (i, proc) in program.procs.list.iter().enumerate() {
            let name = &proc.head.pident;
            if checker.names.contains_key(name) {
                checker.errors.push(ProcUseErr::ProcNameCollision(name.to_owned()));
            } else {
                checker.names.insert(name.to_owned(), i);
            }
        }

        checker.info = vec![Default::default(); program.procs.list.len()];

        checker.walk_commands(&program.main.comms);

        while let Some(i) = checker.used_walk_stack.pop() {
            checker.curr_proc = Some(i);
            checker.walk_commands(&program.procs.list[i].comms);
            checker.curr_proc = None;
        } 

        checker
    }

    pub fn result(self) -> Result<Vec<ProcInfo>, Vec<ProcUseErr>> {
        if self.errors.is_empty() {
            Ok(self.info)
        } else {
            Err(self.errors)
        }
    }

    fn walk_commands(&mut self, commands: &Commands) {
        for command in &commands.list {
            if let Some(curr_i) = self.curr_proc {
                self.info[curr_i].approx_length += 1;
            }
            match command {
                Command::IfElse { then, els, .. } => {
                    self.walk_commands(then);
                    self.walk_commands(els);
                },
                Command::If { then, .. } => {
                    self.walk_commands(then);
                },
                Command::While { body, .. } => {
                    self.walk_commands(body);
                },
                Command::Repeat { body, .. } => {
                    self.walk_commands(body);
                },
                Command::Inlined(body) => {
                    self.walk_commands(body);
                }
                Command::ProcCall(proc) => {
                    let proc_name = &proc.pident;
                    let proc_i = self.names.get(proc_name);
                    let Some(&proc_i) = proc_i else { 
                        self.errors.push(ProcUseErr::UnknownProc(proc_name.to_string()));
                        continue;
                    };

                    if let Some(curr_i) = self.curr_proc {
                        if proc_i >= curr_i {
                            self.errors.push(ProcUseErr::ProcUseBeforeDeclaration(proc_name.to_string()));
                            continue;
                        }
                    }

                    self.info[proc_i].uses += 1;
                    if !self.info[proc_i].visited {
                        self.info[proc_i].visited = true;
                        self.used_walk_stack.push(proc_i);
                    }
                },
                _ => {}
            };
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum VarType  {
    #[default]
    Number,
    Table, 
}

#[derive(Debug, Clone, Default)]
pub struct VarInfo {
    typ: VarType,
    _is_arg: bool,
    is_init: bool,
    uses: u32,
    loop_uses: u32,
    max_loop_depth: u32,
}

/// Sprawdzanie użycia zmiennych:
/// - czy zmienna została zadeklarowana
/// - czy nie ma kolizji nazw zmiennych
/// - czy liczba podanych argumentów do funkcji się zgadza
/// - czy zgadzają się typy zmiennych przy przypisaniach i dawaniu jako argumenty
/// - czy dana zmienna nie została użyta przed zainicjalizowaniem
/// Zakłada że użycie wszystkich procedur jest poprawne i wszystkie nazwy zmiennych są unikalne
#[derive(Debug, Clone, Default)]
pub struct VarUseChecker {
    proc_args: HashMap<String, Vec<VarType>>,
    var_info: HashMap<String, VarInfo>,
    errors: Vec<VarUseError>,
}

#[derive(Debug, Clone)]
pub enum VarUseError {
    TypesDontMatch(String, VarType),
    UseNotDeclared(String),
    UseBeforeInit(String),
    VarNameCollision(String),
    WrongNumberOfArgs(String)
}

impl VarUseChecker {
    pub fn check_prog(prog: &Program) -> VarUseChecker {
        let mut checker = VarUseChecker::default();

        for proc in prog.procs.list.iter() {
            let mut args = vec![];
            for arg in &proc.head.args.list {
                match arg {
                    ast::ArgDecl::Var(_) => args.push(VarType::Number),
                    ast::ArgDecl::Table(_) => args.push(VarType::Table),
                }
            }
            checker.proc_args.insert(proc.head.pident.to_owned(), args);
        }

        for proc in prog.procs.list.iter() {
            for arg in &proc.head.args.list {
                checker.add_var_from_arg(arg);
            }
            for var in &proc.decls.list {
                checker.add_var_from_decl(var);
            }
        }

        for var in &prog.main.decls.list {
            checker.add_var_from_decl(var);
        }

        for proc in prog.procs.list.iter() {
            checker.walk_commands(&proc.comms, 0);
        }

        checker.walk_commands(&prog.main.comms, 0);

        checker
    }

    pub fn result(self) -> Result<HashMap<String, VarInfo>, Vec<VarUseError>> {
        if self.errors.is_empty() {
            Ok(self.var_info)
        } else {
            Err(self.errors)
        }
    }

    fn add_var_from_arg(&mut self, arg: &ast::ArgDecl) {
        match arg {
            ast::ArgDecl::Var(name) => {
                if self.var_info.contains_key(name) {
                    self.errors.push(VarUseError::VarNameCollision(name.to_owned()))
                } else {
                    self.var_info.insert(name.to_owned(), VarInfo { typ: VarType::Number, is_init: true, _is_arg: true, ..Default::default() }); 
                }
            },
            ast::ArgDecl::Table(name) => {
                if self.var_info.contains_key(name) {
                    self.errors.push(VarUseError::VarNameCollision(name.to_owned()))
                } else {
                    self.var_info.insert(name.to_owned(), VarInfo { typ: VarType::Table, is_init: true, _is_arg: true, ..Default::default() }); 
                }
            },
        };
    }
    fn add_var_from_decl(&mut self, var: &ast::Decl) {
        match var {
            ast::Decl::Var(name) => {
                if self.var_info.contains_key(name) {
                    self.errors.push(VarUseError::VarNameCollision(name.to_owned()))
                } else {
                    self.var_info.insert(name.to_owned(), VarInfo { typ: VarType::Number, ..Default::default() }); 
                }
            },
            ast::Decl::Table(name, _) => {
                if self.var_info.contains_key(name) {
                    self.errors.push(VarUseError::VarNameCollision(name.to_owned()))
                } else {
                    self.var_info.insert(name.to_owned(), VarInfo { typ: VarType::Table, ..Default::default() }); 
                }
            },
        };
    }
    fn check_declaration(&mut self, ident: &ast::Ident) -> bool {
        match ident {
            ast::Ident::Var(a) | ast::Ident::TabAccess(a, _) => {
                if !self.var_info.contains_key(a) {
                    self.errors.push(VarUseError::UseNotDeclared(a.to_owned()));
                    false
                } else {
                    true
                }
            },
            ast::Ident::IndirectTab(a, b) => {
                let r1 = if !self.var_info.contains_key(a) {
                    self.errors.push(VarUseError::UseNotDeclared(a.to_owned()));
                    false
                } else {
                    true
                };
                let r2 = if !self.var_info.contains_key(b) {
                    self.errors.push(VarUseError::UseNotDeclared(b.to_owned()));
                    false
                } else {
                    true
                };
                r1 && r2
            },
        }
    }

    fn check_types(&mut self, ident: &ast::Ident) -> bool {
        match ident {
            ast::Ident::Var(a) => {
                let info = &self.var_info[a];
                if info.typ != VarType::Number {
                    self.errors.push(VarUseError::TypesDontMatch(a.to_owned(), VarType::Number));
                    false 
                } else {
                    true
                }
            }, 
            ast::Ident::TabAccess(a, _) => {
                let info = &self.var_info[a];
                if info.typ != VarType::Table {
                    self.errors.push(VarUseError::TypesDontMatch(a.to_owned(), VarType::Table));
                    false 
                } else {
                    true
                }
            },
            ast::Ident::IndirectTab(a, b) => {
                let info = &self.var_info[a];
                let r1 = if info.typ != VarType::Table {
                    self.errors.push(VarUseError::TypesDontMatch(a.to_string(), VarType::Table));
                    false 
                } else {
                    true
                };
                let info = &self.var_info[b];
                let r2 = if info.typ != VarType::Number {
                    self.errors.push(VarUseError::TypesDontMatch(a.to_string(), VarType::Number));
                    false 
                } else {
                    true
                };
                r1 && r2
            },
        }
    }

    fn check_init(&mut self, ident: &ast::Ident, loop_depth: u32) {
        match ident {
            ast::Ident::Var(a) | ast::Ident::TabAccess(a, _) => {
                let info = &self.var_info[a];
                if !info.is_init && loop_depth == 0 {
                    self.errors.push(VarUseError::UseBeforeInit(a.to_owned()));
                }
            },
            ast::Ident::IndirectTab(a, b) => {
                let info = &self.var_info[a];
                if !info.is_init && loop_depth == 0 {
                    self.errors.push(VarUseError::UseBeforeInit(a.to_owned()));
                }
                let info = &self.var_info[b];
                if !info.is_init && loop_depth == 0 {
                    self.errors.push(VarUseError::UseBeforeInit(b.to_owned()));
                }
            },
        }
    }

    fn mark_init(&mut self, ident: &ast::Ident) {
        match ident {
            ast::Ident::Var(a) | ast::Ident::TabAccess(a, _) | ast::Ident::IndirectTab(a, _) => {
                let info = self.var_info.get_mut(a).unwrap();
                info.is_init = true;
            },
        }
    }

    fn increment_uses(&mut self, ident: &ast::Ident, loop_depth: u32) {
        match ident {
            ast::Ident::Var(a) | ast::Ident::TabAccess(a, _) => {
                let info = self.var_info.get_mut(a).unwrap();
                info.uses += 1;
                info.loop_uses += loop_depth;
                info.max_loop_depth = info.max_loop_depth.max(loop_depth);
            },
            ast::Ident::IndirectTab(a, b) => {
                let info = self.var_info.get_mut(a).unwrap();
                info.uses += 1;
                info.loop_uses += loop_depth;
                info.max_loop_depth = info.max_loop_depth.max(loop_depth);

                let info = self.var_info.get_mut(b).unwrap();
                info.uses += 1;
                info.loop_uses += loop_depth;
                info.max_loop_depth = info.max_loop_depth.max(loop_depth);
            },
        }
    }

    fn check_value(&mut self, val: &ast::Value, loop_depth: u32) {
        if let ast::Value::Ident(i) = val {
            if self.check_declaration(i) && self.check_types(i) { 
                self.increment_uses(i, loop_depth); 
            }
        }
    }

    fn check_value_with_init(&mut self, val: &ast::Value, loop_depth: u32) {
        if let ast::Value::Ident(i) = val {
            if self.check_declaration(i) && self.check_types(i) {
                self.check_init(i, loop_depth); 
                self.increment_uses(i, loop_depth); 
            }
        }
    }

    fn check_and_mark_init(&mut self, ident: &ast::Ident, loop_depth: u32) {
        if self.check_declaration(ident) && self.check_types(ident) { 
            self.increment_uses(ident, loop_depth); 
            self.mark_init(ident);
        }
    }

    fn walk_commands(&mut self, commands: &Commands, loop_depth: u32) {
        for command in &commands.list {
            match command {
                Command::IfElse { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::If { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::While { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::Repeat { cond: ast::CondExpr { left, right, .. }, .. } => {
                    self.check_value(left, loop_depth);
                    self.check_value(right, loop_depth);
                },
                Command::Assign(top_left, right) => {
                    self.check_and_mark_init(top_left, loop_depth);
                    match right {
                        ast::MathExpr::Value(val) => {
                            self.check_value_with_init(val, loop_depth);
                        },
                        ast::MathExpr::Binary(ast::BinaryMathExpr { left, right,.. }) => {
                            self.check_value_with_init(left, loop_depth);
                            self.check_value_with_init(right, loop_depth);
                        },
                    }
                },
                Command::ProcCall(p) => {
                    let callee_args = &self.proc_args[&p.pident];
                    let called_args = &p.args;
                    if callee_args.len() != called_args.list.len() {
                        self.errors.push(VarUseError::WrongNumberOfArgs(p.pident.to_string()));
                    }
                    for (&callee_arg, called_arg) in callee_args.iter().zip(called_args.list.iter()) {
                        if let Some(info) = self.var_info.get_mut(called_arg) {
                            info.is_init = true;
                            if info.typ != callee_arg {
                                self.errors.push(VarUseError::TypesDontMatch(called_arg.to_owned(), callee_arg));
                            }
                        } else {
                            self.errors.push(VarUseError::UseNotDeclared(called_arg.to_owned()));
                        }
                    }
                },
                Command::Read(ident) => {
                    self.check_and_mark_init(ident, loop_depth);
                },
                Command::Write(val) => {
                    self.check_value_with_init(val, loop_depth);
                },
                _ => {}
            };
            match command {
                Command::IfElse { then, els, .. } => {
                    self.walk_commands(then, loop_depth);
                    self.walk_commands(els, loop_depth);
                },
                Command::If { then, .. } => {
                    self.walk_commands(then, loop_depth);
                },
                Command::While { body, .. } => {
                    self.walk_commands(body, loop_depth + 1);
                },
                Command::Repeat { body, .. } => {
                    self.walk_commands(body, loop_depth + 1);
                },
                Command::Inlined(body) => {
                    self.walk_commands(body, loop_depth);
                }
                _ => {}
            };
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Pruner;

impl Pruner {
    pub fn prune(prog: &mut Program, info: &mut Vec<ProcInfo>) {
        let indexes = info.iter().enumerate().filter(|&(_, info)| info.uses == 0).map(|(i,_)| i).collect::<Vec<_>>();

        let proc_n = prog.procs.list.len();
        let mut i = proc_n.saturating_sub(1);
        for &to_erase in indexes.iter().rev() {
            while i > to_erase {
                i -= 1;
            }
            prog.procs.list.remove(i);
            info.remove(i);
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Renamer {
    curr_proc: usize
}

impl Renamer {
    pub fn rename(prog: &mut Program) {
        let mut renamer = Renamer::default();

        for (i, proc) in prog.procs.list.iter_mut().enumerate() {
            renamer.curr_proc = i;
            for arg in &mut proc.head.args.list {
                renamer.rename_arg(arg);
            }
            for decl in &mut proc.decls.list {
                renamer.rename_decl(decl);
            }
            renamer.walk_commands(&mut proc.comms);
        }
    }

    pub fn rename_pident(&self, pident: &mut String) {
        pident.push_str(&format!("#{}", self.curr_proc));
    }
    pub fn rename_ident(&self, ident: &mut ast::Ident) {
        match ident {
            Ident::Var(a) | Ident::TabAccess(a, _) => {
                self.rename_pident(a);
            },
            Ident::IndirectTab(a, b) => {
                self.rename_pident(a);
                self.rename_pident(b);
            },
        }
    }
    pub fn rename_val(&self, val: &mut ast::Value) {
        match val {
            ast::Value::Ident(i) => self.rename_ident(i),
            ast::Value::Num(_) => {},
        }
    }
    pub fn rename_decl(&self, decl: &mut ast::Decl) {
        match decl {
            ast::Decl::Var(name) | ast::Decl::Table(name, _) => self.rename_pident(name),
        }
    }
    pub fn rename_arg(&self, arg: &mut ast::ArgDecl) {
        match arg {
            ast::ArgDecl::Var(name) | ast::ArgDecl::Table(name) => self.rename_pident(name),
        }
    }
    pub fn walk_commands(&mut self, commands: &mut Commands) {
        for command in &mut commands.list {
            match command {
                Command::IfElse { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::If { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::While { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::Repeat { cond: ast::CondExpr { left, right, .. }, .. } => {
                    self.rename_val(left);
                    self.rename_val(right);
                },
                Command::Assign(top_left, right) => {
                    self.rename_ident(top_left);
                    match right {
                        ast::MathExpr::Value(val) => {
                            self.rename_val(val);
                        },
                        ast::MathExpr::Binary(ast::BinaryMathExpr { left, right,.. }) => {
                            self.rename_val(left);
                            self.rename_val(right);
                        },
                    }
                },
                Command::ProcCall(p) => {
                    for arg in &mut p.args.list {
                        self.rename_pident(arg);
                    }
                },
                Command::Read(ident) => {
                    self.rename_ident(ident);
                },
                Command::Write(val) => {
                    self.rename_val(val);
                },
                _ => {}
            };

            match command {
                Command::IfElse { then, els, .. } => {
                    self.walk_commands(then);
                    self.walk_commands(els);
                },
                Command::If { then, .. } => {
                    self.walk_commands(then);
                },
                Command::While { body, .. } => {
                    self.walk_commands(body);
                },
                Command::Repeat { body, .. } => {
                    self.walk_commands(body);
                },
                Command::Inlined(body) => {
                    self.walk_commands(body);
                }
                _ => {}
            };
        }
    }
}

#[derive(Debug)]
pub struct Inliner<'a, 'b> {
    gathered_info: &'a mut [ProcInfo],
    program: &'b mut Program,
    names: HashMap<String, usize>,
    proc_args: Vec<Vec<String>>,
    current_proc: Option<usize>,
    current_rename_map: HashMap<String, String>,
}

impl<'a, 'b> Inliner<'a, 'b> {
    pub fn inline_prog(program: &mut Program, gathered_info: &'a mut [ProcInfo]) {
        let mut inliner = Inliner { gathered_info, program, names: HashMap::default(), current_rename_map: HashMap::default(), current_proc: None, proc_args: Vec::new() };

        for (i, proc) in inliner.program.procs.list.iter().enumerate() {
            let name = &proc.head.pident;
            inliner.names.insert(name.to_owned(), i);

            let mut args = Vec::new();

            for arg in &proc.head.args.list {
                match arg {
                    ast::ArgDecl::Var(name) | ast::ArgDecl::Table(name) => {
                        args.push(name.to_owned());
                    },
                }
            }

            inliner.proc_args.push(args);
        }

        for proc_i in 0..inliner.program.procs.list.len() {
            inliner.current_proc = Some(proc_i);
            let proc = &mut inliner.program.procs.list[proc_i];
            let mut comms = std::mem::replace(&mut proc.comms, Commands { list: Vec::new() });
            inliner.walk_commands(&mut comms);
            let proc = &mut inliner.program.procs.list[proc_i];
            std::mem::swap(&mut proc.comms, &mut comms);
        }

        inliner.current_proc = None;
        let main = &mut inliner.program.main;
        let mut comms = std::mem::replace(&mut main.comms, Commands { list: Vec::new() });
        inliner.walk_commands(&mut comms);
        let main = &mut inliner.program.main;
        std::mem::swap(&mut main.comms, &mut comms);

    }

    fn walk_commands(&mut self, commands: &mut Commands) {
        for command in &mut commands.list {
            if let Command::ProcCall(p) = command {
                let i = self.names[&p.pident];
                let info = self.gathered_info[i];
                if info.uses <= 1 {
                    let callee_args = &self.proc_args[i];
                    let rename_map = callee_args.iter().cloned().zip(p.args.list.iter().cloned()).collect::<HashMap<_,_>>();
                    self.current_rename_map = rename_map;

                    let mut comm = self.program.procs.list[i].comms.clone();
                    self.rename(&mut comm);
                    *command = Command::Inlined(comm);

                    self.gathered_info[i].uses -= 1;
                    if let Some(current_proc) = self.current_proc {
                        self.gathered_info[current_proc].approx_length += info.approx_length;
                        for decl_i in 0..self.program.procs.list[i].decls.list.len() {
                            let decl = self.program.procs.list[i].decls.list[decl_i].to_owned();
                            if self.program.procs.list[current_proc].decls.list.contains(&decl) {
                                break;
                            }
                            self.program.procs.list[current_proc].decls.list.push(decl);
                        }
                    } else {
                        for decl_i in 0..self.program.procs.list[i].decls.list.len() {
                            let decl = self.program.procs.list[i].decls.list[decl_i].to_owned();
                            if self.program.main.decls.list.contains(&decl) {
                                break;
                            }
                            self.program.main.decls.list.push(decl);
                        }
                    }
                } 
            };

            match command {
                Command::IfElse { then, els, .. } => {
                    self.walk_commands(then);
                    self.walk_commands(els);
                },
                Command::If { then, .. } => {
                    self.walk_commands(then);
                },
                Command::While { body, .. } => {
                    self.walk_commands(body);
                },
                Command::Repeat { body, .. } => {
                    self.walk_commands(body);
                },
                Command::Inlined(body) => {
                    self.walk_commands(body);
                }
                _ => {}
            };
        }
    }

    pub fn rename_pident(&self, pident: &mut String) {
        if let Some(new_name) = self.current_rename_map.get(pident) {
            *pident = new_name.to_owned();
        }
    }
    pub fn rename_ident(&self, ident: &mut ast::Ident) {
        match ident {
            Ident::Var(a) | Ident::TabAccess(a, _) => {
                self.rename_pident(a);
            },
            Ident::IndirectTab(a, b) => {
                self.rename_pident(a);
                self.rename_pident(b);
            },
        }
    }
    pub fn rename_val(&self, val: &mut ast::Value) {
        match val {
            ast::Value::Ident(i) => self.rename_ident(i),
            ast::Value::Num(_) => {},
        }
    }
    pub fn rename_decl(&self, decl: &mut ast::Decl) {
        match decl {
            ast::Decl::Var(name) | ast::Decl::Table(name, _) => self.rename_pident(name),
        }
    }
    pub fn rename_arg(&self, arg: &mut ast::ArgDecl) {
        match arg {
            ast::ArgDecl::Var(name) | ast::ArgDecl::Table(name) => self.rename_pident(name),
        }
    }
    pub fn rename(&mut self, commands: &mut Commands) {
        for command in &mut commands.list {
            match command {
                Command::IfElse { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::If { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::While { cond: ast::CondExpr { left, right, .. }, .. } |
                Command::Repeat { cond: ast::CondExpr { left, right, .. }, .. } => {
                    self.rename_val(left);
                    self.rename_val(right);
                },
                Command::Assign(top_left, right) => {
                    self.rename_ident(top_left);
                    match right {
                        ast::MathExpr::Value(val) => {
                            self.rename_val(val);
                        },
                        ast::MathExpr::Binary(ast::BinaryMathExpr { left, right,.. }) => {
                            self.rename_val(left);
                            self.rename_val(right);
                        },
                    }
                },
                Command::ProcCall(p) => {
                    for arg in &mut p.args.list {
                        self.rename_pident(arg);
                    }
                },
                Command::Read(ident) => {
                    self.rename_ident(ident);
                },
                Command::Write(val) => {
                    self.rename_val(val);
                },
                _ => {}
            };

            match command {
                Command::IfElse { then, els, .. } => {
                    self.rename(then);
                    self.rename(els);
                },
                Command::If { then, .. } => {
                    self.rename(then);
                },
                Command::While { body, .. } => {
                    self.rename(body);
                },
                Command::Repeat { body, .. } => {
                    self.rename(body);
                },
                Command::Inlined(body) => {
                    self.rename(body);
                }
                _ => {}
            };
        }
    }
}

pub fn optimize_ast(prog: &mut Program) -> bool {
    let proc_info = ProcUseChecker::check_prog(prog).result();

    let mut proc_info = match proc_info {
        Ok(p) => p,
        Err(err) => {
            for err in err {
                match err {
                    ProcUseErr::ProcUseBeforeDeclaration(proc) => {
                        println!("Procedure with name {} was used before decalration", proc);
                    }
                    ProcUseErr::UnknownProc(proc) => {
                        println!("Unknown procedure with name {}", proc);
                    },
                    ProcUseErr::ProcNameCollision(proc) => {
                        println!("Procedure with name {} defined multiple times", proc);
                    },
                }
            }

            return false;
        },
    };
    
    Renamer::rename(prog);

    let var_info = VarUseChecker::check_prog(prog).result();

    if let Err(err) = var_info {
        for err in err {
            match err {
                VarUseError::TypesDontMatch(var, typ) => {
                    println!("Type of var {} doesn't match expected {:?}", var, typ);
                },
                VarUseError::UseNotDeclared(var) => {
                    println!("Use of var {} without declaration", var);
                },
                VarUseError::UseBeforeInit(var) => {
                    println!("Use of var {} before initialization", var);
                },
                VarUseError::VarNameCollision(var) => {
                    println!("Var {} declared multiple times", var);
                },
                VarUseError::WrongNumberOfArgs(proc) => {
                    println!("Too many arguments in call to procedure {}", proc);
                },
            }
        }
        return false;
    }

    Pruner::prune(prog, &mut proc_info);
    Inliner::inline_prog(prog, &mut proc_info);
    Pruner::prune(prog, &mut proc_info);

    true
} 

#[cfg(test)]
mod tests {
    use winnow::Parser;

    use crate::{ast::program, lexer::lex_str};

    use super::*;

    fn gen_prog() -> Program {
        let test = r"
            PROCEDURE pa(a,b) IS
            IN
              a:=a+b;
              b:=a-b;
            END

            PROCEDURE pb(a,b) IS
            IN
              pa(a,b);
              pa(a,b);
            END

            PROCEDURE pc(a,b) IS
            IN
              pb(a,b);
              pb(a,b);
              pb(a,b);
            END

            PROCEDURE pd(a,b) IS
            IN
              pc(a,b);
              pc(a,b);
              pc(a,b);
              pc(a,b);
            END

            PROGRAM IS
              a, b
            IN
              READ a;
              READ b;
              pd(a,b);
              WRITE a;
              WRITE b;
            END";

        let lex = lex_str(test);
        assert!(lex.errors.is_empty());
        let prog = program.parse(&lex.tokens);
        prog.unwrap()
    }

    #[test]
    fn proc_use_checker() {
        let mut prog = gen_prog();

        let mut checker = ProcUseChecker::check_prog(&prog);
        
        dbg!(&checker);

        Pruner::prune(&mut prog, &mut checker.info);

        dbg!(prog);
    }

    #[test]
    fn val_use_checker() {
        let prog = gen_prog();

        let checker = VarUseChecker::check_prog(&prog);

        dbg!(checker);
    }

    #[test]
    fn renamer_test() {
        let mut prog = gen_prog();

        Renamer::rename(&mut prog);

        dbg!(prog);
    }

    #[test]
    fn optimize_test() {
        let mut prog = gen_prog();

        optimize_ast(&mut prog);

        dbg!(prog);
    }
}