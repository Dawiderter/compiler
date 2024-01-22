use std::{collections::HashMap, fmt::Display};

use slotmap::{SlotMap, new_key_type};

use crate::{ast::*, lexer::*};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TempID(usize);

impl TempID {
    pub fn id(&self) -> usize {
        self.0
    }
}

new_key_type! { pub struct LabelID; }

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ProcedureID(usize);

impl ProcedureID {
    pub fn id(&self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy)]
pub enum IRValue {
    Temp(TempID),
    Const(u64),
}

impl Display for IRValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IRValue::Temp(t) => write!(f, "#{}", t.0),
            IRValue::Const(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum IRInstr {
    Assign(TempID, IRValue),
    AssignFromIndexed(TempID, TempID, IRValue),
    AssignToIndexed(TempID, IRValue, IRValue),
    AssignFromAddressIndexed(TempID, TempID, IRValue),
    AssignToAddressIndexed(TempID, IRValue, IRValue),
    AssignToAddress(TempID, IRValue),
    AssignFromAddress(TempID, TempID),
    AssignAdd(TempID, IRValue, IRValue),
    AssignSub(TempID, IRValue, IRValue),
    AssignMul(TempID, IRValue, IRValue),
    AssignDiv(TempID, IRValue, IRValue),
    AssignRem(TempID, IRValue, IRValue),
    Jump(LabelID),
    JumpIfEqual(LabelID, IRValue, IRValue),
    JumpIfNotEqual(LabelID, IRValue, IRValue),
    JumpIfLess(LabelID, IRValue, IRValue),
    JumpIfLessOrEqual(LabelID, IRValue, IRValue),
    PassParamCopy(ProcedureID, TempID, usize),
    PassParamAddress(ProcedureID, TempID, usize),
    Call(ProcedureID),
    Return,
    Halt,
    Read(TempID),
    Write(IRValue),
    Label(LabelID),
}

#[derive(Debug, Clone, Copy)]
pub enum VarType {
    TableArgument,
    Argument,
    TableLocal(u64),
    Local,
}

#[derive(Debug, Clone, Default)]
pub struct VarMap {
    name_to_id: HashMap<String, TempID>,
    id_to_type: Vec<VarType>,
    used_ids: usize,
    argument_count: usize,
}

impl VarMap {
    pub fn add_var(&mut self, name: String, var: VarType) -> TempID {
        let id = TempID(self.id_to_type.len());

        assert!(
            self.used_ids == id.0,
            "Can't add to procedure named vars at this point"
        );

        match var {
            VarType::TableArgument | VarType::Argument => {
                assert!(
                    self.argument_count == id.0,
                    "First add arguments, then locals"
                );
                self.argument_count += 1;
            }
            _ => {}
        }

        self.name_to_id.insert(name, id);
        self.id_to_type.push(var);
        self.used_ids += 1;
        id
    }
    pub fn new_temp(&mut self) -> TempID {
        let id = TempID(self.used_ids);
        self.used_ids += 1;
        id
    }
    pub fn var_name_to_id(&self, name: &str) -> Option<TempID> {
        self.name_to_id.get(name).copied()
    }
    pub fn var_type(&self, id: TempID) -> Option<VarType> {
        self.id_to_type.get(id.0).copied()
    }
    pub fn arg_type(&self, id: usize) -> VarType {
        assert!(id < self.argument_count);
        self.id_to_type[id]
    }
    pub fn arg_count(&self) -> usize {
        self.argument_count
    }
    pub fn iter_vars(&self) -> impl Iterator<Item = VarType> + '_ {
        self.id_to_type.iter().copied()
    }
    pub fn total_tmp(&self) -> usize {
        self.used_ids - self.id_to_type.len()
    }
}

#[derive(Debug, Clone, Default)]
pub struct IRProcedure {
    pub name: String,
    pub vars: VarMap,
    pub labels: SlotMap<LabelID, String>,
    pub instructions: Vec<IRInstr>,
}

#[derive(Debug, Clone)]
pub enum IRGenErr {
    VariableNotDeclared,
    ProcedureNotDeclared,
    VariableWrongType,
    ProcedureArgWrongType,
    ProcedureWrongNumberOfArgs,
    ConstIndexOutOfRange,
}

impl IRProcedure {
    // fn verify_type(&self, name: &str, exp_typ: VarTypeVerify) -> Result<TempID, IRProcGenErr> {
    //     let id = self
    //         .vars
    //         .var_name_to_id(name)
    //         .ok_or(IRProcGenErr::VariableNotDeclared)?;
    //     let typ = self.vars.var_type(id).unwrap();
    //     matches!(
    //         (typ, exp_typ),
    //         (VarType::TableArgument, VarTypeVerify::Table)
    //             | (VarType::Table(_), VarTypeVerify::Table)
    //             | (VarType::Argument, VarTypeVerify::Value)
    //             | (VarType::Value, VarTypeVerify::Value)
    //     )
    //     .then_some(id)
    //     .ok_or(IRProcGenErr::VariableWrongType)
    // }

    fn verify_exists(&self, name: &str) -> Result<TempID, IRGenErr> {
        self.vars
            .var_name_to_id(name)
            .ok_or(IRGenErr::VariableNotDeclared)
    }

    fn push_instr(&mut self, instr: IRInstr) {
        self.instructions.push(instr);
    }

    fn add_label(&mut self, label: &str) -> LabelID {
        let number = self.labels.len();
        let unique_name = format!("{}@{}", label, number);
        self.labels.insert(unique_name)
    }

    fn generate_access(&mut self, value: Value) -> Result<IRValue, IRGenErr> {
        match value {
            Value::Num(n) => Ok(IRValue::Const(n)),
            Value::Ident(Ident::Var(name)) => {
                let id = self.verify_exists(&name)?;
                match self.vars.var_type(id).unwrap() {
                    VarType::Argument => {
                        let tmp = self.vars.new_temp();
                        self.push_instr(IRInstr::AssignFromAddress(tmp, id));
                        Ok(IRValue::Temp(tmp))
                    }
                    VarType::Local => Ok(IRValue::Temp(id)),
                    _ => Err(IRGenErr::VariableWrongType),
                }
            }
            Value::Ident(Ident::TabAccess(name, n)) => {
                let id = self.verify_exists(&name)?;
                match self.vars.var_type(id).unwrap() {
                    VarType::TableLocal(size) => {
                        if n >= size {
                            return Err(IRGenErr::ConstIndexOutOfRange);
                        }
                        let tmp = self.vars.new_temp();
                        self.push_instr(IRInstr::AssignFromIndexed(tmp, id, IRValue::Const(n)));
                        Ok(IRValue::Temp(tmp))
                    }
                    VarType::TableArgument => {
                        let tmp = self.vars.new_temp();
                        self.push_instr(IRInstr::AssignFromAddressIndexed(
                            tmp,
                            id,
                            IRValue::Const(n),
                        ));
                        Ok(IRValue::Temp(tmp))
                    }
                    _ => Err(IRGenErr::VariableWrongType),
                }
            }
            Value::Ident(Ident::IndirectTab(name_a, name_b)) => {
                let id_a = self.verify_exists(&name_a)?;
                let id_b = self.verify_exists(&name_b)?;
                let id_tmp_b = match self.vars.var_type(id_b).unwrap() {
                    VarType::Argument => {
                        let tmp = self.vars.new_temp();
                        self.push_instr(IRInstr::AssignFromAddress(tmp, id_b));
                        Ok(tmp)
                    }
                    VarType::Local => Ok(id_b),
                    _ => Err(IRGenErr::VariableWrongType),
                }?;

                match self.vars.var_type(id_a).unwrap() {
                    VarType::TableLocal(_) => {
                        let tmp = self.vars.new_temp();
                        self.push_instr(IRInstr::AssignFromIndexed(
                            tmp,
                            id_a,
                            IRValue::Temp(id_tmp_b),
                        ));
                        Ok(IRValue::Temp(tmp))
                    }
                    VarType::TableArgument => {
                        let tmp = self.vars.new_temp();
                        self.push_instr(IRInstr::AssignFromAddressIndexed(
                            tmp,
                            id_a,
                            IRValue::Temp(id_tmp_b),
                        ));
                        Ok(IRValue::Temp(tmp))
                    }
                    _ => Err(IRGenErr::VariableWrongType),
                }
            }
        }
    }

    fn generate_set(&mut self, to: Ident, from: TempID) -> Result<(), IRGenErr> {
        let from = IRValue::Temp(from);

        match to {
            Ident::Var(name) => {
                let left_id = self.verify_exists(&name)?;
                match self.vars.var_type(left_id).unwrap() {
                    VarType::Argument => {
                        self.push_instr(IRInstr::AssignToAddress(left_id, from));
                    }
                    VarType::Local => {
                        self.push_instr(IRInstr::Assign(left_id, from));
                    }
                    _ => return Err(IRGenErr::VariableWrongType),
                }
            }
            Ident::TabAccess(name, n) => {
                let left_id = self.verify_exists(&name)?;
                match self.vars.var_type(left_id).unwrap() {
                    VarType::TableLocal(size) => {
                        if n >= size {
                            return Err(IRGenErr::ConstIndexOutOfRange);
                        }
                        self.push_instr(IRInstr::AssignToIndexed(left_id, IRValue::Const(n), from));
                    }
                    VarType::TableArgument => {
                        self.push_instr(IRInstr::AssignToAddressIndexed(
                            left_id,
                            IRValue::Const(n),
                            from,
                        ));
                    }
                    _ => return Err(IRGenErr::VariableWrongType),
                }
            }
            Ident::IndirectTab(name_a, name_b) => {
                let id_a = self.verify_exists(&name_a)?;
                let id_b = self.verify_exists(&name_b)?;
                let id_tmp_b = match self.vars.var_type(id_b).unwrap() {
                    VarType::Argument => {
                        let tmp = self.vars.new_temp();
                        self.push_instr(IRInstr::AssignFromAddress(tmp, id_b));
                        Ok(tmp)
                    }
                    VarType::Local => Ok(id_b),
                    _ => Err(IRGenErr::VariableWrongType),
                }?;

                match self.vars.var_type(id_a).unwrap() {
                    VarType::TableLocal(_) => {
                        self.push_instr(IRInstr::AssignToIndexed(
                            id_a,
                            IRValue::Temp(id_tmp_b),
                            from,
                        ));
                    }
                    VarType::TableArgument => {
                        self.push_instr(IRInstr::AssignToAddressIndexed(
                            id_a,
                            IRValue::Temp(id_tmp_b),
                            from,
                        ));
                    }
                    _ => return Err(IRGenErr::VariableWrongType),
                }
            }
        }

        Ok(())
    }

    fn generate_assign(&mut self, left: Ident, right: MathExpr) -> Result<(), IRGenErr> {
        // Stwórz nowe temporary do którego przypiszemy wartość
        let left_temp_id = self.vars.new_temp();

        match right {
            MathExpr::Value(v) => {
                let right_val = self.generate_access(v)?;
                self.push_instr(IRInstr::Assign(left_temp_id, right_val));
            }
            MathExpr::Binary(BinaryMathExpr { left, right, op }) => {
                let rl_val = self.generate_access(left)?;
                let rr_val = self.generate_access(right)?;
                match op {
                    MathOperator::Add => {
                        self.push_instr(IRInstr::AssignAdd(left_temp_id, rl_val, rr_val))
                    }
                    MathOperator::Sub => {
                        self.push_instr(IRInstr::AssignSub(left_temp_id, rl_val, rr_val))
                    }
                    MathOperator::Mul => {
                        self.push_instr(IRInstr::AssignMul(left_temp_id, rl_val, rr_val))
                    }
                    MathOperator::Div => {
                        self.push_instr(IRInstr::AssignDiv(left_temp_id, rl_val, rr_val))
                    }
                    MathOperator::Rem => {
                        self.push_instr(IRInstr::AssignRem(left_temp_id, rl_val, rr_val))
                    }
                }
            }
        }

        // Wynik działania znajduje się teraz w left_temp_id
        // Teraz trzeba go przenieść do left_id

        self.generate_set(left, left_temp_id)?;

        Ok(())
    }

    fn generate_jump_on_true(&mut self, cond: CondExpr, label: LabelID) -> Result<(), IRGenErr> {
        let CondExpr { left, right, op } = cond;
        let left_id = self.generate_access(left)?;
        let right_id = self.generate_access(right)?;
        match op {
            CondOperator::Equal => {
                self.push_instr(IRInstr::JumpIfEqual(label, left_id, right_id));
            }
            CondOperator::NotEqual => {
                self.push_instr(IRInstr::JumpIfNotEqual(label, left_id, right_id));
            }
            CondOperator::Lesser => {
                self.push_instr(IRInstr::JumpIfLess(label, left_id, right_id));
            }
            CondOperator::LesserEq => {
                self.push_instr(IRInstr::JumpIfLessOrEqual(label, left_id, right_id));
            }
            CondOperator::Greater => {
                self.push_instr(IRInstr::JumpIfLess(label, right_id, left_id));
            }
            CondOperator::GreaterEq => {
                self.push_instr(IRInstr::JumpIfLessOrEqual(label, right_id, left_id));
            }
        }
        Ok(())
    }

    fn generate_jump_on_false(&mut self, cond: CondExpr, label: LabelID) -> Result<(), IRGenErr> {
        let CondExpr { left, right, op } = cond;
        let op = op.negate();
        self.generate_jump_on_true(CondExpr { left, right, op }, label)
    }

    fn generate_if(
        &mut self,
        cond: CondExpr,
        then: Commands,
        program_so_far: &IRProgram,
    ) -> Result<(), IRGenErr> {
        // JUMP TO END IF COND FALSE
        // ..body
        // END
        // ..rest

        let label_id = self.add_label("ENDIF");
        self.generate_jump_on_false(cond, label_id)?;

        self.generate_commands(then, program_so_far)?;

        self.push_instr(IRInstr::Label(label_id));

        Ok(())
    }

    fn generate_if_else(
        &mut self,
        cond: CondExpr,
        then: Commands,
        els: Commands,
        program_so_far: &IRProgram,
    ) -> Result<(), IRGenErr> {
        // JUMP TO ELSE IF COND FALSE
        // ..body
        // JUMP END
        // ELSE:
        // ..else
        // END:
        // ..rest

        let else_id = self.add_label("ELSE");
        let end_id = self.add_label("ENDELSEIF");

        self.generate_jump_on_false(cond, else_id)?;
        self.generate_commands(then, program_so_far)?;
        self.push_instr(IRInstr::Jump(end_id));

        self.push_instr(IRInstr::Label(else_id));
        self.generate_commands(els, program_so_far)?;

        self.push_instr(IRInstr::Label(end_id));

        Ok(())
    }

    fn generate_while(
        &mut self,
        cond: CondExpr,
        body: Commands,
        program_so_far: &IRProgram,
    ) -> Result<(), IRGenErr> {
        // BEGIN:
        // JUMP TO END IF COND FALSE
        // ..body
        // JUMP TO BEGIN
        // END:
        // ..rest

        let begin_id = self.add_label("BEGINWHILE");
        let end_id = self.add_label("ENDWHILE");

        self.push_instr(IRInstr::Label(begin_id));

        self.generate_jump_on_false(cond, end_id)?;
        self.generate_commands(body, program_so_far)?;
        self.push_instr(IRInstr::Jump(begin_id));

        self.push_instr(IRInstr::Label(end_id));

        Ok(())
    }

    fn generate_repeat(
        &mut self,
        cond: CondExpr,
        body: Commands,
        program_so_far: &IRProgram,
    ) -> Result<(), IRGenErr> {
        // BEGIN:
        // ..body
        // JUMP TO BEGIN IF COND FALSE
        // ..rest
        let begin_id = self.add_label("BEGINREPEAT");

        self.push_instr(IRInstr::Label(begin_id));
        self.generate_commands(body, program_so_far)?;
        self.generate_jump_on_false(cond, begin_id)?;

        Ok(())
    }

    fn generate_read(&mut self, ident: Ident) -> Result<(), IRGenErr> {
        let temp_id = self.vars.new_temp();
        self.push_instr(IRInstr::Read(temp_id));
        self.generate_set(ident, temp_id)?;
        Ok(())
    }

    fn generate_write(&mut self, value: Value) -> Result<(), IRGenErr> {
        let result = self.generate_access(value)?;
        self.push_instr(IRInstr::Write(result));
        Ok(())
    }

    fn generate_call(
        &mut self,
        proc_call: ProcCall,
        program_so_far: &IRProgram,
    ) -> Result<(), IRGenErr> {
        let ProcCall {
            pident,
            args: Args { list },
        } = proc_call;

        let called_proc_id = program_so_far.verify_exists(&pident)?;
        let called_proc = program_so_far.get_proc(called_proc_id);

        if called_proc.vars.arg_count() != list.len() {
            return Err(IRGenErr::ProcedureWrongNumberOfArgs);
        }

        #[allow(clippy::needless_range_loop)]
        for i in 0..called_proc.vars.arg_count() {
            let proc_arg_type = called_proc.vars.arg_type(i);

            let called_name = &list[i];
            let called_arg = self.verify_exists(called_name)?;
            let called_arg_type = self.vars.var_type(called_arg).unwrap();

            match (called_arg_type, proc_arg_type) {
                (VarType::TableArgument, VarType::TableArgument) => {
                    self.push_instr(IRInstr::PassParamCopy(called_proc_id, called_arg, i))
                }
                (VarType::TableLocal(_), VarType::TableArgument) => {
                    self.push_instr(IRInstr::PassParamAddress(called_proc_id, called_arg, i))
                }
                (VarType::Argument, VarType::Argument) => {
                    self.push_instr(IRInstr::PassParamCopy(called_proc_id, called_arg, i))
                }
                (VarType::Local, VarType::Argument) => {
                    self.push_instr(IRInstr::PassParamAddress(called_proc_id, called_arg, i))
                }
                _ => {
                    return Err(IRGenErr::ProcedureArgWrongType);
                }
            }
        }

        self.push_instr(IRInstr::Call(called_proc_id));

        Ok(())
    }

    fn generate_commands(
        &mut self,
        commands: Commands,
        program_so_far: &IRProgram,
    ) -> Result<(), IRGenErr> {
        for command in commands.list {
            match command {
                Command::Assign(l, r) => self.generate_assign(l, r)?,
                Command::If { cond, then } => self.generate_if(cond, then, program_so_far)?,
                Command::IfElse { cond, then, els } => {
                    self.generate_if_else(cond, then, els, program_so_far)?
                }
                Command::While { cond, body } => self.generate_while(cond, body, program_so_far)?,
                Command::Repeat { cond, body } => {
                    self.generate_repeat(cond, body, program_so_far)?
                }
                Command::Read(x) => self.generate_read(x)?,
                Command::Write(x) => self.generate_write(x)?,
                Command::ProcCall(c) => self.generate_call(c, program_so_far)?,
            }
        }
        Ok(())
    }

    pub fn generate_main(main: Main, program_so_far: &IRProgram) -> Result<IRProcedure, IRGenErr> {
        let Main { decls, comms } = main;
        let mut ir_procedure = IRProcedure {
            name: "main".to_string(),
            ..Default::default()
        };

        for decl in decls.list {
            match decl {
                Decl::Var(v) => {
                    ir_procedure.vars.add_var(v, VarType::Local);
                }
                Decl::Table(t, n) => {
                    ir_procedure.vars.add_var(t, VarType::TableLocal(n));
                }
            }
        }

        ir_procedure.generate_commands(comms, program_so_far)?;

        ir_procedure.push_instr(IRInstr::Halt);

        Ok(ir_procedure)
    }

    pub fn generate(proc: Procedure, program_so_far: &IRProgram) -> Result<IRProcedure, IRGenErr> {
        let Procedure { head, decls, comms } = proc;

        let mut ir_procedure = IRProcedure {
            name: head.pident,
            ..Default::default()
        };

        for arg in head.args.list {
            match arg {
                ArgDecl::Var(v) => {
                    ir_procedure.vars.add_var(v, VarType::Argument);
                }
                ArgDecl::Table(t) => {
                    ir_procedure.vars.add_var(t, VarType::TableArgument);
                }
            }
        }

        for decl in decls.list {
            match decl {
                Decl::Var(v) => {
                    ir_procedure.vars.add_var(v, VarType::Local);
                }
                Decl::Table(t, n) => {
                    ir_procedure.vars.add_var(t, VarType::TableLocal(n));
                }
            }
        }

        ir_procedure.generate_commands(comms, program_so_far)?;

        ir_procedure.push_instr(IRInstr::Return);

        Ok(ir_procedure)
    }
}

#[derive(Debug, Clone, Default)]
pub struct IRProgram {
    pub proc_names_to_id: HashMap<String, ProcedureID>,
    pub procedures: Vec<IRProcedure>,
    pub main: IRProcedure,
}

impl IRProgram {
    fn add_procedure(&mut self, proc_name: String, proc: IRProcedure) {
        let id = ProcedureID(self.procedures.len());
        self.proc_names_to_id.insert(proc_name, id);
        self.procedures.push(proc);
    }
    fn verify_exists(&self, proc_name: &str) -> Result<ProcedureID, IRGenErr> {
        self.proc_names_to_id
            .get(proc_name)
            .copied()
            .ok_or(IRGenErr::ProcedureNotDeclared)
    }
    fn get_proc(&self, id: ProcedureID) -> &IRProcedure {
        &self.procedures[id.0]
    }
    pub fn generate(program: Program) -> Result<IRProgram, IRGenErr> {
        let mut ir_program = IRProgram::default();

        let Program { procs, main } = program;

        for proc in procs.list {
            let name = proc.head.pident.clone();

            let ir_proc = IRProcedure::generate(proc, &ir_program)?;

            ir_program.add_procedure(name, ir_proc);
        }

        let main = IRProcedure::generate_main(main, &ir_program)?;

        ir_program.main = main;

        Ok(ir_program)
    }
}

impl Display for IRProcedure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "proc {}", self.name)?;

        writeln!(f, "(")?;
        for (name, &id) in &self.vars.name_to_id {
            writeln!(
                f,
                "   {} = #{} type: {:?}",
                name,
                id.0,
                self.vars.var_type(id).unwrap()
            )?;
        }
        writeln!(f, ")")?;

        for instr in &self.instructions {
            write!(f, "  ")?;
            match instr {
                IRInstr::Assign(l, r) => {
                    writeln!(f, "#{} = {}", l.0, r)?;
                }
                IRInstr::AssignFromIndexed(l, r, i) => {
                    writeln!(f, "#{} = #{}[{}]", l.0, r.0, i)?;
                }
                IRInstr::AssignToIndexed(l, i, r) => {
                    writeln!(f, "#{}[{}] = {}", l.0, i, r)?;
                }
                IRInstr::AssignFromAddressIndexed(l, r, i) => {
                    writeln!(f, "#{} = &#{}[{}]", l.0, r.0, i)?;
                }
                IRInstr::AssignToAddressIndexed(l, i, r) => {
                    writeln!(f, "&#{}[{}] = {}", l.0, i, r)?;
                }
                IRInstr::AssignToAddress(l, r) => {
                    writeln!(f, "&#{} = {}", l.0, r)?;
                }
                IRInstr::AssignFromAddress(l, r) => {
                    writeln!(f, "#{} = &#{}", l.0, r.0)?;
                }
                IRInstr::AssignAdd(l, r1, r2) => {
                    writeln!(f, "#{} = {} + {}", l.0, r1, r2)?;
                }
                IRInstr::AssignSub(l, r1, r2) => {
                    writeln!(f, "#{} = {} - {}", l.0, r1, r2)?;
                }
                IRInstr::AssignMul(l, r1, r2) => {
                    writeln!(f, "#{} = {} * {}", l.0, r1, r2)?;
                }
                IRInstr::AssignDiv(l, r1, r2) => {
                    writeln!(f, "#{} = {} / {}", l.0, r1, r2)?;
                }
                IRInstr::AssignRem(l, r1, r2) => {
                    writeln!(f, "#{} = {} % {}", l.0, r1, r2)?;
                }
                IRInstr::Jump(label) => {
                    writeln!(f, "goto {}", self.labels[*label])?;
                }
                IRInstr::JumpIfEqual(label, l, r) => {
                    writeln!(f, "goto {} if {} = {}", self.labels[*label], l, r)?;
                }
                IRInstr::JumpIfNotEqual(label, l, r) => {
                    writeln!(f, "goto {} if {} != {}", self.labels[*label], l, r)?;
                }
                IRInstr::JumpIfLess(label, l, r) => {
                    writeln!(f, "goto {} if {} < {}", self.labels[*label], l, r)?;
                }
                IRInstr::JumpIfLessOrEqual(label, l, r) => {
                    writeln!(f, "goto {} if {} <= {}", self.labels[*label], l, r)?;
                }
                IRInstr::Label(label) => {
                    writeln!(f, "{}:", self.labels[*label])?;
                }
                IRInstr::Return => {
                    writeln!(f, "return")?;
                }
                IRInstr::Halt => {
                    writeln!(f, "halt")?;
                }
                IRInstr::Call(proc) => {
                    writeln!(f, "call fn@{}", proc.0)?;
                }
                IRInstr::PassParamCopy(proc, x, i) => {
                    writeln!(f, "pass #{} to fn@{} [{}]", x.0, proc.0,i)?;
                }
                IRInstr::PassParamAddress(proc, x, i) => {
                    writeln!(f, "pass &#{} to fn@{} [{}]", x.0, proc.0,i)?;
                }
                IRInstr::Read(x) => {
                    writeln!(f, "read to #{}", x.0)?;
                }
                IRInstr::Write(x) => {
                    writeln!(f, "write {}", x)?;
                }
            }
        }

        Ok(())
    }
}

impl Display for IRProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, proc) in self.procedures.iter().enumerate() {
            writeln!(f, "fn@{}", i)?;
            writeln!(f, "{}", proc)?;
        }

        writeln!(f, "{}", self.main)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use winnow::Parser;

    use super::*;

    #[test]
    fn test() {
        let input = include_str!("./../examples2023/ir_tests.imp");
        let tokens = lex_str(input);
        assert!(tokens.errors.is_empty());
        let prog = program.parse(&tokens.tokens).unwrap();
        let ir_prog = IRProgram::generate(prog).unwrap();
        println!("{}", ir_prog);
    }
}
