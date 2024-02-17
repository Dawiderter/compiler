use std::{collections::HashMap, fmt::Display};

use slotmap::{SecondaryMap, SlotMap};

use crate::{
    mir::{CondOp, MathOp, MirInstr, MirLabel, MirValue, MirVar, MirVarInfo, MirVarType},
    mir_analysis::{MemorySlot, Register, SpillInfo},
};

#[derive(Debug, Clone, Copy)]
pub enum TargetLabel {
    Resolved(u64),
    Unresolved(MirLabel),
}

#[derive(Debug, Clone)]
pub enum MachInstr {
    /// pobraną liczbę zapisuje w rejestrze ra oraz k ← k + 1
    Read,
    /// wyświetla zawartość rejestru ra oraz k ← k + 1
    Write,
    /// ra ← prx oraz k ← k + 1
    Load(Register),
    /// prx ← ra oraz k ← k + 1
    Store(Register),
    /// ra ← ra + rx oraz k ← k + 1
    Add(Register),
    /// ra ← max{ra − rx, 0} oraz k ← k + 1
    Sub(Register),
    /// ra ← rx oraz k ← k + 1
    Get(Register),
    /// rx ← ra oraz k ← k + 1
    Put(Register),
    /// rx ← 0 oraz k ← k + 1
    Rst(Register),
    /// rx ← rx + 1 oraz k ← k + 1
    Inc(Register),
    /// rx ← max{rx − 1, 0} oraz k ← k + 1
    Dec(Register),
    /// rx ← 2 ∗ rx oraz k ← k + 1
    Shl(Register),
    /// rx ← ⌊rx/2⌋ oraz k ← k + 1
    Shr(Register),
    /// k ← j
    Jump(TargetLabel),
    /// jeśli ra > 0 to k ← j, w p.p. k ← k + 1
    JPos(TargetLabel),
    /// jeśli ra = 0 to k ← j, w p.p. k ← k + 1
    JZero(TargetLabel),
    /// rx ← k oraz k ← k + 1
    Strk(Register),
    /// k ← rx
    Jumpr(Register),
    /// zatrzymaj program
    Halt,
    /// dodatkowe "niby-instrukcje"
    Const(Register, u64),
    Lea(Register, MemorySlot),
    Label(MirLabel),
    Comment(String),
}

#[derive(Debug, Clone, Default)]
pub struct MachProgramBuilder {
    pub instr: Vec<MachInstr>,
    pub variables: SlotMap<MirVar, MirVarInfo>,
    pub spills: SecondaryMap<MirVar, SpillInfo>,
    pub memory: SlotMap<MemorySlot, u64>,
    pub labels: SlotMap<MirLabel, ()>,
    pub memcache: HashMap<MirVar, MemorySlot>,
}

impl MachProgramBuilder {
    const JUMP_RETURN_SKIP: u64 = 3;

    fn push(&mut self, instr: MachInstr) {
        self.instr.push(instr)
    }

    fn new_label(&mut self) -> MirLabel {
        self.labels.insert(())
    }

    fn load_val_to_a(&mut self, value: MirValue) {
        match value {
            MirValue::Var(t) => match self.spills[t] {
                SpillInfo::Spilled(mem) => {
                    self.push(MachInstr::Lea(Register::A, mem));
                    self.push(MachInstr::Load(Register::A));
                }
                SpillInfo::Reg(reg) => {
                    self.push(MachInstr::Get(reg));
                }
            },
            MirValue::Const(n) => {
                self.push(MachInstr::Const(Register::A, n));
            }
        }
    }

    fn get_cached(&mut self, var: MirVar) -> MemorySlot {
        if let Some(&slot) = self.memcache.get(&var) {
            slot
        } else {
            let size = match self.variables[var].typ {
                MirVarType::TableLocal(n) => n,
                _ => 1,
            };
            let new_mem = self.memory.insert(size);
            self.memcache.insert(var, new_mem);
            new_mem
        }
    }

    fn build_instr(&mut self, instr: MirInstr) {
        match instr {
            MirInstr::Load(var_a, var_b) => {
                let spill = self.spills[var_a];
                match spill {
                    SpillInfo::Spilled(mem) => {
                        self.push(MachInstr::Lea(Register::B, mem));
                        self.load_val_to_a(MirValue::Var(var_b));
                        self.push(MachInstr::Load(Register::A));
                        self.push(MachInstr::Store(Register::B));
                    }
                    SpillInfo::Reg(reg) => {
                        self.load_val_to_a(MirValue::Var(var_b));
                        self.push(MachInstr::Load(Register::A));
                        self.push(MachInstr::Put(reg));
                    }
                }
            }
            MirInstr::Store(var_a, val) => {
                self.load_val_to_a(MirValue::Var(var_a));
                self.push(MachInstr::Put(Register::B));
                self.load_val_to_a(val);
                self.push(MachInstr::Store(Register::B));
            }
            MirInstr::Assign(var_a, val) => {
                let spill = self.spills[var_a];
                match spill {
                    SpillInfo::Spilled(mem) => {
                        self.push(MachInstr::Lea(Register::B, mem));
                        self.load_val_to_a(val);
                        self.push(MachInstr::Store(Register::B));
                    }
                    SpillInfo::Reg(reg) => {
                        self.load_val_to_a(val);
                        self.push(MachInstr::Put(reg));
                    }
                }
            }
            MirInstr::AssignExpr(var, left, op, right) => {
                match op {
                    MathOp::Add => self.build_add(left, right),
                    MathOp::Sub => self.build_sub(left, right),
                    MathOp::Mul => self.build_mul(left, right),
                    MathOp::Div => self.build_div(left, right),
                    MathOp::Rem => self.build_rem(left, right),
                }
                let spill = self.spills[var];
                match spill {
                    SpillInfo::Spilled(mem) => {
                        self.push(MachInstr::Lea(Register::B, mem));
                        self.push(MachInstr::Store(Register::B));
                    }
                    SpillInfo::Reg(reg) => {
                        self.push(MachInstr::Put(reg));
                    }
                }
            }
            MirInstr::LoadAddress(var_a, var_b) => {
                let spill_a = self.spills[var_a];
                let spill_b = self.spills[var_b];
                match (spill_a, spill_b) {
                    (SpillInfo::Spilled(mem_a), SpillInfo::Spilled(mem_b)) => {
                        self.push(MachInstr::Lea(Register::B, mem_a));
                        self.push(MachInstr::Lea(Register::A, mem_b));
                        self.push(MachInstr::Store(Register::B));
                    }
                    (SpillInfo::Spilled(mem_a), SpillInfo::Reg(reg_b)) => {
                        let cached_b = self.get_cached(var_b);

                        self.push(MachInstr::Lea(Register::B, cached_b));
                        self.push(MachInstr::Get(reg_b));
                        self.push(MachInstr::Store(Register::B));

                        self.push(MachInstr::Get(Register::B));
                        self.push(MachInstr::Lea(Register::B, mem_a));
                        self.push(MachInstr::Store(Register::B));
                    }
                    (SpillInfo::Reg(reg_a), SpillInfo::Spilled(mem_b)) => {
                        self.push(MachInstr::Lea(reg_a, mem_b));
                    }
                    (SpillInfo::Reg(reg_a), SpillInfo::Reg(reg_b)) => {
                        let cached_b = self.get_cached(var_b);

                        self.push(MachInstr::Lea(Register::B, cached_b));
                        self.push(MachInstr::Get(reg_b));
                        self.push(MachInstr::Store(Register::B));

                        self.push(MachInstr::Get(Register::B));
                        self.push(MachInstr::Put(reg_a));
                    }
                }
            }
            MirInstr::Jump(label, _) => {
                self.push(MachInstr::Jump(TargetLabel::Unresolved(label)));
            }
            MirInstr::JumpCond(label, left, op, right) => match op {
                CondOp::IsEqual => self.build_jeq(left, right, label),
                CondOp::IsNotEqual => self.build_jneq(left, right, label),
                CondOp::IsLess => self.build_jle(left, right, label),
                CondOp::IsLessEqual => self.build_jleq(left, right, label),
            },
            MirInstr::Strk(var) => {
                let spill = self.spills[var];
                match spill {
                    SpillInfo::Spilled(mem) => {
                        self.push(MachInstr::Lea(Register::B, mem));
                        self.push(MachInstr::Strk(Register::A));
                        self.push(MachInstr::Store(Register::B));
                    }
                    SpillInfo::Reg(reg) => {
                        self.push(MachInstr::Strk(reg));
                        self.push(MachInstr::Inc(Register::A));
                    }
                }
            }
            MirInstr::JumpReturn(var) => {
                self.load_val_to_a(MirValue::Var(var));
                for _ in 0..Self::JUMP_RETURN_SKIP {
                    self.push(MachInstr::Inc(Register::A));
                }
                self.push(MachInstr::Jumpr(Register::A));
            }
            MirInstr::Read(var) => {
                let spill = self.spills[var];
                match spill {
                    SpillInfo::Spilled(mem) => {
                        self.push(MachInstr::Lea(Register::B, mem));
                        self.push(MachInstr::Read);
                        self.push(MachInstr::Store(Register::B));
                    }
                    SpillInfo::Reg(reg) => {
                        self.push(MachInstr::Read);
                        self.push(MachInstr::Put(reg));
                    }
                }
            }
            MirInstr::Write(val) => {
                self.load_val_to_a(val);
                self.push(MachInstr::Write);
            }
            MirInstr::Label(l) => {
                self.push(MachInstr::Label(l));
            }
            MirInstr::Halt => {
                self.push(MachInstr::Halt);
            }
            MirInstr::Noop => {}
            MirInstr::NoopRead(_) => {}
        }
    }

    fn build_add(&mut self, left: MirValue, right: MirValue) {
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(left);
        self.push(MachInstr::Add(Register::B));
    }

    fn build_sub(&mut self, left: MirValue, right: MirValue) {
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(left);
        self.push(MachInstr::Sub(Register::B));
    }

    fn build_mul(&mut self, left: MirValue, right: MirValue) {
        let begin = self.new_label();
        let even = self.new_label();
        let end = self.new_label();
        // Ładowanie right do C, left do B
        self.load_val_to_a(left);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::C));
        // Wynik będzie w D
        self.push(MachInstr::Rst(Register::D));
        // While c > 0
        self.push(MachInstr::Label(begin));
        self.push(MachInstr::Get(Register::C));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(end)));
        // y/2 * 2 + 1 -> 1 - y%2 -> 1 parzysta lub - nieparzysta
        self.push(MachInstr::Shr(Register::A));
        self.push(MachInstr::Shl(Register::A));
        self.push(MachInstr::Inc(Register::A));
        self.push(MachInstr::Sub(Register::C));
        // if y nieparzysta to d = d + b
        self.push(MachInstr::JPos(TargetLabel::Unresolved(even)));
        self.push(MachInstr::Get(Register::D));
        self.push(MachInstr::Add(Register::B));
        self.push(MachInstr::Put(Register::D));
        self.push(MachInstr::Label(even));
        // b << 1 i c >> 1
        self.push(MachInstr::Shl(Register::B));
        self.push(MachInstr::Shr(Register::C));
        self.push(MachInstr::Jump(TargetLabel::Unresolved(begin)));
        self.push(MachInstr::Label(end));
        // Ładowanie adresu l do B
        // Zapisz
        self.push(MachInstr::Get(Register::D));
    }

    fn build_div(&mut self, left: MirValue, right: MirValue) {
        let begin_counting = self.new_label();
        let end_counting = self.new_label();
        let begin_div = self.new_label();
        let end_div = self.new_label();
        let cant_sub = self.new_label();
        // Ładowanie right do C, left do B
        self.load_val_to_a(left);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::C));
        // Licznik wielkości dzielnika
        self.push(MachInstr::Rst(Register::D));
        // Wynik dzielenia
        self.push(MachInstr::Rst(Register::E));
        // if c == 0 skip
        self.push(MachInstr::Get(Register::C));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
        // while c <= b
        self.push(MachInstr::Label(begin_counting));
        self.push(MachInstr::Get(Register::C));
        self.push(MachInstr::Sub(Register::B));
        self.push(MachInstr::JPos(TargetLabel::Unresolved(end_counting)));
        self.push(MachInstr::Shl(Register::C));
        self.push(MachInstr::Inc(Register::D));
        self.push(MachInstr::Jump(TargetLabel::Unresolved(begin_counting)));
        self.push(MachInstr::Label(end_counting));
        // while e > 0
        self.push(MachInstr::Label(begin_div));
        self.push(MachInstr::Get(Register::D));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
        self.push(MachInstr::Dec(Register::D));
        self.push(MachInstr::Shr(Register::C));
        self.push(MachInstr::Get(Register::B));
        self.push(MachInstr::Inc(Register::A));
        self.push(MachInstr::Sub(Register::C));
        self.push(MachInstr::Shl(Register::E));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(cant_sub)));
        self.push(MachInstr::Dec(Register::A));
        self.push(MachInstr::Put(Register::B));
        self.push(MachInstr::Inc(Register::E));
        self.push(MachInstr::Label(cant_sub));
        self.push(MachInstr::Jump(TargetLabel::Unresolved(begin_div)));
        self.push(MachInstr::Label(end_div));

        self.push(MachInstr::Get(Register::E));
    }

    fn build_rem(&mut self, left: MirValue, right: MirValue) {
        let begin_counting = self.new_label();
        let end_counting = self.new_label();
        let begin_div = self.new_label();
        let end_div = self.new_label();
        let cant_sub = self.new_label();
        // Ładowanie rr do C
        self.push(MachInstr::Rst(Register::B));
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::C));
        // Licznik wielkości dzielnika
        self.push(MachInstr::Rst(Register::D));
        // Wynik dzielenia
        self.push(MachInstr::Rst(Register::E));
        // if c == 0 skip
        self.push(MachInstr::Get(Register::C));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
        // Ładowanie rl do B
        self.load_val_to_a(left);
        self.push(MachInstr::Put(Register::B));
        // while c <= b
        self.push(MachInstr::Label(begin_counting));
        self.push(MachInstr::Get(Register::C));
        self.push(MachInstr::Sub(Register::B));
        self.push(MachInstr::JPos(TargetLabel::Unresolved(end_counting)));
        self.push(MachInstr::Shl(Register::C));
        self.push(MachInstr::Inc(Register::D));
        self.push(MachInstr::Jump(TargetLabel::Unresolved(begin_counting)));
        self.push(MachInstr::Label(end_counting));
        // while e > 0
        self.push(MachInstr::Label(begin_div));
        self.push(MachInstr::Get(Register::D));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
        self.push(MachInstr::Dec(Register::D));
        self.push(MachInstr::Shr(Register::C));
        self.push(MachInstr::Get(Register::B));
        self.push(MachInstr::Inc(Register::A));
        self.push(MachInstr::Sub(Register::C));
        self.push(MachInstr::Shl(Register::E));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(cant_sub)));
        self.push(MachInstr::Dec(Register::A));
        self.push(MachInstr::Put(Register::B));
        self.push(MachInstr::Inc(Register::E));
        self.push(MachInstr::Label(cant_sub));
        // self.push(MachInstr::Get(Register::B));
        // self.push(MachInstr::Write);
        self.push(MachInstr::Jump(TargetLabel::Unresolved(begin_div)));
        self.push(MachInstr::Label(end_div));

        // Zapisz
        self.push(MachInstr::Get(Register::B));
    }

    fn build_jeq(&mut self, left: MirValue, right: MirValue, target: MirLabel) {
        // END label
        let end = self.new_label();
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(left);
        self.push(MachInstr::Put(Register::C));
        // l - r
        self.push(MachInstr::Sub(Register::B));
        self.push(MachInstr::JPos(TargetLabel::Unresolved(end)));
        // r - l
        self.push(MachInstr::Get(Register::B));
        self.push(MachInstr::Sub(Register::C));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(target)));

        self.push(MachInstr::Label(end));
    }

    fn build_jneq(&mut self, left: MirValue, right: MirValue, target: MirLabel) {
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(left);
        self.push(MachInstr::Put(Register::C));
        // l - r
        self.push(MachInstr::Sub(Register::B));
        self.push(MachInstr::JPos(TargetLabel::Unresolved(target)));
        // r - l
        self.push(MachInstr::Get(Register::B));
        self.push(MachInstr::Sub(Register::C));
        self.push(MachInstr::JPos(TargetLabel::Unresolved(target)));
    }

    fn build_jle(&mut self, left: MirValue, right: MirValue, target: MirLabel) {
        // l < r -> r - l > 0
        self.load_val_to_a(left);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(right);
        self.push(MachInstr::Sub(Register::B));
        self.push(MachInstr::JPos(TargetLabel::Unresolved(target)));
    }

    fn build_jleq(&mut self, left: MirValue, right: MirValue, target: MirLabel) {
        // l <= r -> l - r <= 0
        self.load_val_to_a(right);
        self.push(MachInstr::Put(Register::B));
        self.load_val_to_a(left);
        self.push(MachInstr::Sub(Register::B));
        self.push(MachInstr::JZero(TargetLabel::Unresolved(target)));
    }

    fn memory_alloc(&mut self) {
        let mut max = 0;
        for (_, size) in &mut self.memory {
            let pos = max;
            max += *size;
            *size = pos;
        }
    }

    fn const_in_reg(&mut self, n: u64, reg: Register) {
        self.push(MachInstr::Rst(reg));
        if n > 0 {
            let x = n.ilog2();
            let mut mask = (1 << x) >> 1;
            self.push(MachInstr::Inc(reg));
            while mask != 0 {
                self.push(MachInstr::Shl(reg));
                if (mask & n) > 0 {
                    self.push(MachInstr::Inc(reg));
                }
                mask >>= 1;
            }
        }
    }

    fn rewrite_illegals(&mut self) {
        let old_instr = std::mem::take(&mut self.instr);

        for instr in old_instr {
            match instr {
                MachInstr::Const(reg, n) => {
                    self.const_in_reg(n, reg);
                }
                MachInstr::Lea(reg, slot) => {
                    let pos = self.memory[slot];
                    self.const_in_reg(pos, reg);
                }
                instr => self.push(instr),
            }
        }
    }

    fn resolve_labels(&mut self) {
        let mut map = HashMap::new();
        let mut i = 0;
        for instr in &self.instr {
            match instr {
                MachInstr::Label(l) => {
                    map.insert(*l, i);
                }
                MachInstr::Comment(_) => {}
                _ => {
                    i += 1;
                }
            }
        }

        for instr in &mut self.instr {
            match instr {
                MachInstr::Jump(l) | MachInstr::JPos(l) | MachInstr::JZero(l) => {
                    let TargetLabel::Unresolved(ml) = l else { continue; };
                    let j = map[&*ml];
                    *l = TargetLabel::Resolved(j);
                }
                _ => {}
            }
        }
    }

    pub fn build(&mut self, instructions: &[MirInstr]) {
        for &instr in instructions {
            self.build_instr(instr);
        }

        self.memory_alloc();
        
        self.rewrite_illegals();

        self.resolve_labels();
    }
}

impl Display for TargetLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TargetLabel::Resolved(j) => write!(f, "{}", j),
            TargetLabel::Unresolved(l) => write!(f, "{}", l),
        }
    }
}

impl Display for MachProgramBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for instr in &self.instr {
            match instr {
                MachInstr::Read => {
                    writeln!(f, "READ")?;
                }
                MachInstr::Write => {
                    writeln!(f, "WRITE")?;
                }
                MachInstr::Load(x) => {
                    writeln!(f, "LOAD {}", x)?;
                }
                MachInstr::Store(x) => {
                    writeln!(f, "STORE {}", x)?;
                }
                MachInstr::Add(x) => {
                    writeln!(f, "ADD {}", x)?;
                }
                MachInstr::Sub(x) => {
                    writeln!(f, "SUB {}", x)?;
                }
                MachInstr::Get(x) => {
                    writeln!(f, "GET {}", x)?;
                }
                MachInstr::Put(x) => {
                    writeln!(f, "PUT {}", x)?;
                }
                MachInstr::Rst(x) => {
                    writeln!(f, "RST {}", x)?;
                }
                MachInstr::Inc(x) => {
                    writeln!(f, "INC {}", x)?;
                }
                MachInstr::Dec(x) => {
                    writeln!(f, "DEC {}", x)?;
                }
                MachInstr::Shl(x) => {
                    writeln!(f, "SHL {}", x)?;
                }
                MachInstr::Shr(x) => {
                    writeln!(f, "SHR {}", x)?;
                }
                MachInstr::Jump(l) => {
                    writeln!(f, "JUMP {}", l)?;
                }
                MachInstr::JPos(l) => {
                    writeln!(f, "JPOS {}", l)?;
                }
                MachInstr::JZero(l) => {
                    writeln!(f, "JZERO {}", l)?;
                }
                MachInstr::Strk(x) => {
                    writeln!(f, "STRK {}", x)?;
                }
                MachInstr::Jumpr(x) => {
                    writeln!(f, "JUMPR {}", x)?;
                }
                MachInstr::Halt => {
                    writeln!(f, "HALT")?;
                }
                MachInstr::Label(l) => {
                    writeln!(f, "# {}", l)?;
                }
                MachInstr::Comment(s) => {
                    writeln!(f, "# {}", s)?;
                }
                MachInstr::Const(reg, c) => {
                    writeln!(f, "CONST {} {}", reg, c)?;
                }
                MachInstr::Lea(reg, addr) => {
                    writeln!(f, "LEA {} {}", reg, addr)?;
                }
            }
        }

        Ok(())
    }
}


