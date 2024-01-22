use std::{collections::HashMap, fmt::Display};

use crate::triaddress::{
    IRInstr, IRProgram, IRValue, LabelID, TempID, VarMap, VarType,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Register(usize);

impl Register {
    pub const A: Self = Register(0);
    pub const B: Self = Register(1);
    pub const C: Self = Register(2);
    pub const D: Self = Register(3);
    pub const E: Self = Register(4);
    pub const F: Self = Register(5);
    pub const G: Self = Register(6);
    pub const H: Self = Register(7);
    pub fn tmp(id: usize) -> Register {
        Register(id + 8)
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MachLabelID(usize);

#[derive(Debug, Clone, Copy)]
pub enum TargetLabel {
    Resolved(u64),
    Unresolved(MachLabelID),
}

#[derive(Debug, Clone, Default)]
pub struct MachLabelMap {
    map: HashMap<(usize, LabelID), MachLabelID>,
    proc_map: HashMap<usize, MachLabelID>,
    used_ids: usize,
}

impl MachLabelMap {
    pub fn gen_new(&mut self) -> MachLabelID {
        let id = self.used_ids;
        self.used_ids += 1;
        MachLabelID(id)
    }
    pub fn add_get_label(&mut self, slot: usize, label: LabelID) -> MachLabelID {
        if let Some(id) = self.map.get(&(slot, label)) {
            *id
        } else {
            let id = MachLabelID(self.used_ids);
            self.used_ids += 1;
            self.map.insert((slot, label), id);
            id
        }
    }
    pub fn add_proc(&mut self, proc: usize) -> MachLabelID {
        let id = MachLabelID(self.used_ids);
        self.used_ids += 1;

        let res = self.proc_map.insert(proc, id);
        assert!(res.is_none(), "Already put that proc");
        id
    }
    pub fn get_proc(&mut self, proc: usize) -> MachLabelID {
        self.proc_map[&proc]
    }
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
    Label(MachLabelID),
    Comment(String),
}

#[derive(Debug, Clone, Default)]
pub struct ActivationRecords {
    // Position of ith variable in jth procedure
    pos: Vec<Vec<u64>>,
}

impl ActivationRecords {
    fn position_of(&self, slot: usize, var_slot: usize) -> u64 {
        let record = &self.pos[slot];

        record[var_slot + 1]
    }

    fn position_of_return(&self, slot: usize) -> u64 {
        let record = &self.pos[slot];
        record[0]
    }

    fn add_record(&mut self, slot: usize, record: Vec<u64>) {
        if slot >= self.pos.len() {
            self.pos.resize(slot + 1, Vec::new());
        }
        self.pos[slot] = record;
    }

    fn fix_records(&mut self) {
        let mut max = 0;
        for record in self.pos.iter_mut() {
            assert!(!record.is_empty(), "Empty record");
            assert!(*record.first().unwrap() == 0, "Already fixed record");
            for a in record.iter_mut() {
                *a += max;
            }
            max = *record.last().unwrap() + 1;
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct MachProgram {
    instr: Vec<MachInstr>,
    labels: MachLabelMap,
    records: ActivationRecords,
}

impl MachProgram {
    const JUMP_RETURN_SKIP: u64 = 3;

    fn vars_to_record(vars: &VarMap) -> Vec<u64> {
        let mut vec = vec![0];
        let mut s = 1;
        for var in vars.iter_vars() {
            vec.push(s);
            s += match var {
                VarType::TableLocal(n) => n,
                VarType::Local | VarType::Argument | VarType::TableArgument => 1,
            }
        }
        for _ in 0..vars.total_tmp() {
            vec.push(s);
            s += 1
        }
        vec
    }

    fn push_instr(&mut self, instr: MachInstr) {
        self.instr.push(instr)
    }

    fn generate_const_in_a(&mut self, n: u64) {
        self.push_instr(MachInstr::Comment(format!("Generate const {}", n)));
        self.push_instr(MachInstr::Rst(Register::A));
        if n > 0 {
            let x = n.ilog2();
            let mut mask = (1 << x) >> 1;
            self.push_instr(MachInstr::Inc(Register::A));
            while mask != 0 {
                self.push_instr(MachInstr::Shl(Register::A));
                if (mask & n) > 0 {
                    self.push_instr(MachInstr::Inc(Register::A));
                }
                mask >>= 1;
            }
        }
    }

    fn load_to_reg(&mut self, proc_slot: usize, reg: Register, value: IRValue) {
        self.push_instr(MachInstr::Comment(format!("Load {} to {}", value, reg)));
        match value {
            IRValue::Temp(t) => {
                let pos = self.records.position_of(proc_slot, t.id());
                self.generate_const_in_a(pos);
                self.push_instr(MachInstr::Load(Register::A));
            }
            IRValue::Const(n) => {
                self.generate_const_in_a(n);
            }
        }
        if reg != Register::A {
            self.push_instr(MachInstr::Put(reg));
        }
    }

    fn load_address_to_reg(&mut self, proc_slot: usize, reg: Register, var: TempID) {
        let addr = self.records.position_of(proc_slot, var.id());
        self.generate_const_in_a(addr);
        if reg != Register::A {
            self.push_instr(MachInstr::Put(reg));
        }
    }

    pub fn generate_instr(&mut self, proc_slot: usize, instr: IRInstr) {
        match instr {
            IRInstr::Assign(l, r) => {
                self.push_instr(MachInstr::Comment(format!("Do #{} = {}", l.id(), r)));
                // Generowanie adresu l w B
                self.load_address_to_reg(proc_slot, Register::B, l);
                // Ładowanie wartości r do A
                self.load_to_reg(proc_slot, Register::A, r);
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::B));
            }
            IRInstr::AssignFromIndexed(l, r, i) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Do #{} = #{}[{}]",
                    l.id(),
                    r.id(),
                    i
                )));
                // Generowanie adresu l w C
                self.load_address_to_reg(proc_slot, Register::C, l);
                // Ładowanie adresu r do B, wartości i do A, dodanie i zapisanie w B
                self.load_address_to_reg(proc_slot, Register::B, r);
                self.load_to_reg(proc_slot, Register::A, i);
                self.push_instr(MachInstr::Add(Register::B));
                self.push_instr(MachInstr::Put(Register::B));
                // Załadowanie wartości pod wyliczonym adresem
                self.push_instr(MachInstr::Load(Register::B));
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::C));
            }
            IRInstr::AssignToIndexed(l, i, r) => {
                self.push_instr(MachInstr::Comment(format!("Do #{}[{}] = {}", l.id(), i, r)));
                // Ładowanie i do B, generowanie l w A, dodanie i zapisanie w B
                self.load_to_reg(proc_slot, Register::B, i);
                self.load_address_to_reg(proc_slot, Register::A, l);
                self.push_instr(MachInstr::Add(Register::B));
                self.push_instr(MachInstr::Put(Register::B));
                // Ładowanie r do A
                self.load_to_reg(proc_slot, Register::A, r);
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::B));
            }
            IRInstr::AssignFromAddressIndexed(l, r, i) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Do #{} = &#{}[{}]",
                    l.id(),
                    r.id(),
                    i
                )));
                // Generowanie adresu l w C
                self.load_address_to_reg(proc_slot, Register::C, l);
                // Ładowanie r do B, i do A, dodanie i zapisanie w B
                self.load_to_reg(proc_slot, Register::B, IRValue::Temp(r));
                self.load_to_reg(proc_slot, Register::A, i);
                self.push_instr(MachInstr::Add(Register::B));
                self.push_instr(MachInstr::Put(Register::B));
                // Załadowanie wartości pod adresem
                self.push_instr(MachInstr::Load(Register::B));
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::C));
            }
            IRInstr::AssignToAddressIndexed(l, i, r) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Do &#{}[{}] = {}",
                    l.id(),
                    i,
                    r
                )));
                // Ładowanie i do B, generowanie l w A, dodanie i zapisanie w B
                self.load_to_reg(proc_slot, Register::B, i);
                self.load_to_reg(proc_slot, Register::A, IRValue::Temp(l));
                self.push_instr(MachInstr::Add(Register::B));
                self.push_instr(MachInstr::Put(Register::B));
                // Ładowanie r do A
                self.load_to_reg(proc_slot, Register::A, r);
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::B));
            }
            IRInstr::AssignToAddress(l, r) => {
                self.push_instr(MachInstr::Comment(format!("Do &#{} = {}", l.id(), r)));
                // Ładowanie l do B
                self.load_to_reg(proc_slot, Register::B, IRValue::Temp(l));
                // Ładowanie r do A
                self.load_to_reg(proc_slot, Register::A, r);
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::B));
            }
            IRInstr::AssignFromAddress(l, r) => {
                self.push_instr(MachInstr::Comment(format!("Do #{} = &#{}", l.id(), r.id())));
                // Ładowanie adresu l do B
                self.load_address_to_reg(proc_slot, Register::B, l);
                // Ładowanie r do A
                self.load_to_reg(proc_slot, Register::A, IRValue::Temp(r));
                // Ładowanie wartości pod adresem
                self.push_instr(MachInstr::Load(Register::A));
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::B));
            }
            IRInstr::AssignAdd(l, rl, rr) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Do #{} = {} + {}",
                    l.id(),
                    rl,
                    rr
                )));
                // Ładowanie adresu l do C
                self.load_address_to_reg(proc_slot, Register::C, l);
                // Ładowanie rr do B, rl do A i dodanie
                self.load_to_reg(proc_slot, Register::B, rr);
                self.load_to_reg(proc_slot, Register::A, rl);
                self.push_instr(MachInstr::Add(Register::B));
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::C));
            }
            IRInstr::AssignSub(l, rl, rr) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Do #{} = {} - {}",
                    l.id(),
                    rl,
                    rr
                )));
                // Ładowanie adresu l do C
                self.load_address_to_reg(proc_slot, Register::C, l);
                // Ładowanie rr do B, rl do A i dodanie
                self.load_to_reg(proc_slot, Register::B, rr);
                self.load_to_reg(proc_slot, Register::A, rl);
                self.push_instr(MachInstr::Sub(Register::B));
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::C));
            }
            IRInstr::AssignMul(l, rl, rr) => {
                let begin = self.labels.gen_new();
                let even = self.labels.gen_new();
                let end = self.labels.gen_new();
                // Ładowanie rr do C, rl do B
                self.load_to_reg(proc_slot, Register::B, rl);
                self.load_to_reg(proc_slot, Register::C, rr);
                // Wynik będzie w D
                self.push_instr(MachInstr::Rst(Register::D));
                // While c > 0 
                self.push_instr(MachInstr::Label(begin));
                self.push_instr(MachInstr::Get(Register::C));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(end)));
                // y/2 * 2 + 1 -> 1 - y%2 -> 1 parzysta lub - nieparzysta
                self.push_instr(MachInstr::Shr(Register::A));
                self.push_instr(MachInstr::Shl(Register::A));
                self.push_instr(MachInstr::Inc(Register::A));
                self.push_instr(MachInstr::Sub(Register::C));
                // if y nieparzysta to d = d + b
                self.push_instr(MachInstr::JPos(TargetLabel::Unresolved(even)));
                self.push_instr(MachInstr::Get(Register::D));
                self.push_instr(MachInstr::Add(Register::B));
                self.push_instr(MachInstr::Put(Register::D));
                self.push_instr(MachInstr::Label(even));
                // b << 1 i c >> 1
                self.push_instr(MachInstr::Shl(Register::B));
                self.push_instr(MachInstr::Shr(Register::C));
                self.push_instr(MachInstr::Jump(TargetLabel::Unresolved(begin)));
                self.push_instr(MachInstr::Label(end));
                // Ładowanie adresu l do B
                self.load_address_to_reg(proc_slot, Register::B, l);
                // Zapisz
                self.push_instr(MachInstr::Get(Register::D));
                self.push_instr(MachInstr::Store(Register::B));
            },
            IRInstr::AssignDiv(l, rl, rr) => {
                let begin_counting = self.labels.gen_new();
                let end_counting = self.labels.gen_new();
                let begin_div = self.labels.gen_new();
                let end_div = self.labels.gen_new();
                let cant_sub = self.labels.gen_new();
                // Ładowanie rr do C, rl do B
                self.load_to_reg(proc_slot, Register::B, rl);
                self.load_to_reg(proc_slot, Register::C, rr);
                // Licznik wielkości dzielnika
                self.push_instr(MachInstr::Rst(Register::D));
                // Wynik dzielenia
                self.push_instr(MachInstr::Rst(Register::E));
                // if c == 0 skip
                self.push_instr(MachInstr::Get(Register::C));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
                // while c <= b
                self.push_instr(MachInstr::Label(begin_counting));
                self.push_instr(MachInstr::Get(Register::C));
                self.push_instr(MachInstr::Sub(Register::B));
                self.push_instr(MachInstr::JPos(TargetLabel::Unresolved(end_counting)));
                self.push_instr(MachInstr::Shl(Register::C));
                self.push_instr(MachInstr::Inc(Register::D));
                self.push_instr(MachInstr::Jump(TargetLabel::Unresolved(begin_counting)));
                self.push_instr(MachInstr::Label(end_counting));
                // while e > 0
                self.push_instr(MachInstr::Label(begin_div));
                self.push_instr(MachInstr::Get(Register::D));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
                self.push_instr(MachInstr::Dec(Register::D));
                self.push_instr(MachInstr::Shr(Register::C));
                self.push_instr(MachInstr::Get(Register::B));
                self.push_instr(MachInstr::Inc(Register::A));
                self.push_instr(MachInstr::Sub(Register::C));
                self.push_instr(MachInstr::Shl(Register::E));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(cant_sub)));
                self.push_instr(MachInstr::Dec(Register::A));
                self.push_instr(MachInstr::Put(Register::B));
                self.push_instr(MachInstr::Inc(Register::E));
                self.push_instr(MachInstr::Label(cant_sub));
                self.push_instr(MachInstr::Jump(TargetLabel::Unresolved(begin_div)));
                self.push_instr(MachInstr::Label(end_div));
                // Ładowanie adresu l do B
                self.load_address_to_reg(proc_slot, Register::B, l);
                // Zapisz
                self.push_instr(MachInstr::Get(Register::E));
                self.push_instr(MachInstr::Store(Register::B));
            },
            IRInstr::AssignRem(l, rl, rr) => {
                let begin_counting = self.labels.gen_new();
                let end_counting = self.labels.gen_new();
                let begin_div = self.labels.gen_new();
                let end_div = self.labels.gen_new();
                let cant_sub = self.labels.gen_new();
                // Ładowanie rr do C
                self.push_instr(MachInstr::Rst(Register::B));
                self.load_to_reg(proc_slot, Register::C, rr);
                // Licznik wielkości dzielnika
                self.push_instr(MachInstr::Rst(Register::D));
                // Wynik dzielenia
                self.push_instr(MachInstr::Rst(Register::E));
                // if c == 0 skip
                self.push_instr(MachInstr::Get(Register::C));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
                // Ładowanie rl do B
                self.load_to_reg(proc_slot, Register::B, rl);
                // while c <= b
                self.push_instr(MachInstr::Label(begin_counting));
                self.push_instr(MachInstr::Get(Register::C));
                self.push_instr(MachInstr::Sub(Register::B));
                self.push_instr(MachInstr::JPos(TargetLabel::Unresolved(end_counting)));
                self.push_instr(MachInstr::Shl(Register::C));
                self.push_instr(MachInstr::Inc(Register::D));
                self.push_instr(MachInstr::Jump(TargetLabel::Unresolved(begin_counting)));
                self.push_instr(MachInstr::Label(end_counting));
                // while e > 0
                self.push_instr(MachInstr::Label(begin_div));
                self.push_instr(MachInstr::Get(Register::D));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(end_div)));
                self.push_instr(MachInstr::Dec(Register::D));
                self.push_instr(MachInstr::Shr(Register::C));
                self.push_instr(MachInstr::Get(Register::B));
                self.push_instr(MachInstr::Inc(Register::A));
                self.push_instr(MachInstr::Sub(Register::C));
                self.push_instr(MachInstr::Shl(Register::E));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(cant_sub)));
                self.push_instr(MachInstr::Dec(Register::A));
                self.push_instr(MachInstr::Put(Register::B));
                self.push_instr(MachInstr::Inc(Register::E));
                self.push_instr(MachInstr::Label(cant_sub));
                self.push_instr(MachInstr::Jump(TargetLabel::Unresolved(begin_div)));
                self.push_instr(MachInstr::Label(end_div));
                // Ładowanie adresu l do B
                self.load_address_to_reg(proc_slot, Register::C, l);
                // Zapisz
                self.push_instr(MachInstr::Get(Register::B));
                self.push_instr(MachInstr::Store(Register::C));
            },
            IRInstr::Jump(label) => {
                let ml = self.labels.add_get_label(proc_slot, label);
                self.push_instr(MachInstr::Jump(TargetLabel::Unresolved(ml)));
            }
            IRInstr::JumpIfEqual(label, l, r) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Jump @{:?} if {} = {}",
                    label,
                    l,
                    r
                )));
                // END label
                let end = self.labels.gen_new();
                let target = self.labels.add_get_label(proc_slot, label);
                // l == r -> l - r == 0 -> l - r >= 0 && l - r <= 0 
                // -> r - l <= 0 && l - r <= 0
                // IF l - r > 0 JUMP END
                // IF r - l == 0 JUMP TARGET
                // END
                self.load_to_reg(proc_slot, Register::B, r);
                self.load_to_reg(proc_slot, Register::A, l);
                self.push_instr(MachInstr::Put(Register::C));
                // l - r
                self.push_instr(MachInstr::Sub(Register::B));
                self.push_instr(MachInstr::JPos(TargetLabel::Unresolved(end)));
                // r - l
                self.push_instr(MachInstr::Get(Register::B));
                self.push_instr(MachInstr::Sub(Register::C));
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(target)));

                self.push_instr(MachInstr::Label(end));
            }
            IRInstr::JumpIfNotEqual(label, l, r) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Jump @{:?} if {} = {}",
                    label,
                    l,
                    r
                )));
                let target = self.labels.add_get_label(proc_slot, label);
                // l != r -> l - r != 0 -> l - r < 0 || l - r > 0 
                // r - l > 0 || l - r > 0
                // IF l - r > 0 JUMP TARGET
                // END label
                // IF r - l > 0 JUMP TARGET
                // END
                self.load_to_reg(proc_slot, Register::B, r);
                self.load_to_reg(proc_slot, Register::A, l);
                self.push_instr(MachInstr::Put(Register::C));
                // l - r
                self.push_instr(MachInstr::Sub(Register::B));
                self.push_instr(MachInstr::JPos(TargetLabel::Unresolved(target)));
                // r - l
                self.push_instr(MachInstr::Get(Register::B));
                self.push_instr(MachInstr::Sub(Register::C));
                self.push_instr(MachInstr::JPos(TargetLabel::Unresolved(target)));

            }
            IRInstr::JumpIfLess(label, l, r) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Jump @{:?} if {} < {}",
                    label,
                    l,
                    r
                )));
                // l < r -> r - l > 0
                self.load_to_reg(proc_slot, Register::B, l);
                self.load_to_reg(proc_slot, Register::A, r);
                self.push_instr(MachInstr::Sub(Register::B));
                let ml = self.labels.add_get_label(proc_slot, label);
                self.push_instr(MachInstr::JPos(TargetLabel::Unresolved(ml)));
            }
            IRInstr::JumpIfLessOrEqual(label, l, r) => {
                self.push_instr(MachInstr::Comment(format!(
                    "Jump @{:?} if {} <= {}",
                    label,
                    l,
                    r
                )));
                // l <= r -> l - r <= 0
                self.load_to_reg(proc_slot, Register::B, r);
                self.load_to_reg(proc_slot, Register::A, l);
                self.push_instr(MachInstr::Sub(Register::B));
                let ml = self.labels.add_get_label(proc_slot, label);
                self.push_instr(MachInstr::JZero(TargetLabel::Unresolved(ml)));
            }
            IRInstr::PassParamCopy(p, x, i) => {
                let addr = self.records.position_of(p.id() + 1, i);
                self.generate_const_in_a(addr);
                self.push_instr(MachInstr::Put(Register::B));
                self.load_to_reg(proc_slot, Register::A, IRValue::Temp(x));
                self.push_instr(MachInstr::Store(Register::B));
            },
            IRInstr::PassParamAddress(p, x, i) => {
                let addr = self.records.position_of(p.id() + 1, i);
                self.generate_const_in_a(addr);
                self.push_instr(MachInstr::Put(Register::B));
                self.load_address_to_reg(proc_slot, Register::A, x);
                self.push_instr(MachInstr::Store(Register::B));
            },
            IRInstr::Call(p) => {
                let l = self.labels.get_proc(p.id() + 1);
                // Załaduj adres na powrót wywoływanej proc do B
                let addr = self.records.position_of_return(p.id() + 1);
                self.generate_const_in_a(addr);
                self.push_instr(MachInstr::Put(Register::B));
                // Zapisz tam ten adres (ważne że to ten adres!)
                self.push_instr(MachInstr::Strk(Register::A));
                self.push_instr(MachInstr::Store(Register::B));
                self.push_instr(MachInstr::Jump(TargetLabel::Unresolved(l)));
                // +3 jest istotne! stała JUMP_RETURN_SKIP
            }
            IRInstr::Return => {
                // Załaduj adres na powrót tej proc do B i ten powrót do A
                let addr = self.records.position_of_return(proc_slot);
                self.generate_const_in_a(addr);
                self.push_instr(MachInstr::Put(Register::B));
                self.push_instr(MachInstr::Load(Register::B));
                for _ in 0..Self::JUMP_RETURN_SKIP {
                    self.push_instr(MachInstr::Inc(Register::A));
                }
                // Wracanie
                self.push_instr(MachInstr::Jumpr(Register::A));
            },
            IRInstr::Halt => {
                self.push_instr(MachInstr::Halt);
            }
            IRInstr::Read(x) => {
                self.push_instr(MachInstr::Comment(format!("Do read to #{}", x.id(),)));
                // Ładowanie adresu x do B
                self.load_address_to_reg(proc_slot, Register::B, x);
                // Czytanie do A
                self.push_instr(MachInstr::Read);
                // Zapisanie
                self.push_instr(MachInstr::Store(Register::B));
            }
            IRInstr::Write(x) => {
                self.push_instr(MachInstr::Comment(format!("Do write {}", x,)));
                // Ładowanie wartości x do A
                self.load_to_reg(proc_slot, Register::A, x);
                // Wypisywanie A
                self.push_instr(MachInstr::Write);
            }
            IRInstr::Label(label) => {
                let ml = self.labels.add_get_label(proc_slot, label);
                self.push_instr(MachInstr::Label(ml));
            }
        }
    }

    pub fn resolve_labels(&mut self) {
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
                    let i = map[ml];
                    *l = TargetLabel::Resolved(i);
                }
                _ => {}
            }
        }
    }

    pub fn generate(ir: IRProgram) -> MachProgram {
        let mut prog = MachProgram::default();
        let IRProgram {
            procedures, main, ..
        } = ir;

        let main_record = Self::vars_to_record(&main.vars);
        prog.records.add_record(0, main_record);
        prog.labels.add_proc(0);

        for (slot, proc) in procedures.iter().enumerate() {
            let record = Self::vars_to_record(&proc.vars);
            prog.records.add_record(slot + 1, record);
            prog.labels.add_proc(slot + 1);
        }

        prog.records.fix_records();

        for instr in main.instructions {
            prog.generate_instr(0, instr);
        }

        for (i, proc) in procedures.into_iter().enumerate() {
            let l = prog.labels.get_proc(i + 1);
            prog.push_instr(MachInstr::Label(l));
            for instr in proc.instructions {
                prog.generate_instr(i + 1, instr);
            }
        }

        prog.resolve_labels();

        prog
    }
}

impl Display for TargetLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TargetLabel::Resolved(j) => write!(f, "{}", j),
            TargetLabel::Unresolved(l) => write!(f, "m@{}", l.0),
        }
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            0 => write!(f, "a"),
            1 => write!(f, "b"),
            2 => write!(f, "c"),
            3 => write!(f, "d"),
            4 => write!(f, "e"),
            5 => write!(f, "f"),
            6 => write!(f, "g"),
            7 => write!(f, "h"),
            i => write!(f, "#{}", i),
        }
    }
}

impl Display for MachProgram {
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
                    writeln!(f, "# m@{}", l.0)?;
                }
                MachInstr::Comment(s) => {
                    writeln!(f, "# {}", s)?;
                }
            }
        }

        Ok(())
    }
}

impl Display for ActivationRecords {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, record) in self.pos.iter().enumerate() {
            if i == 0 {
                writeln!(f, "main")?;
            } else {
                writeln!(f, "fn@{}", i - 1)?;
            }
            for (j, pos) in record.iter().enumerate() {
                if j == 0 {
                    writeln!(f, "   return: {}", pos)?;
                } else {
                    writeln!(f, "    {}: {}", j, pos)?;
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{env::args, fs::read_to_string};

    use winnow::Parser;

    use crate::{
        ast::{program, ok_with_report},
        lexer::{lex_str, report_lex_errors},
    };

    use super::*;

    #[test]
    fn gen_const() {
        let mut program = MachProgram::default();

        program.generate_const_in_a(0);

        program.push_instr(MachInstr::Halt);

        program.generate_const_in_a(1);

        program.push_instr(MachInstr::Halt);

        program.generate_const_in_a(16);

        program.push_instr(MachInstr::Halt);

        program.generate_const_in_a(33);

        program.push_instr(MachInstr::Halt);

        println!("{}", program);
    }

    #[test]
    fn test() {
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
        println!("{}", mach.records);
        println!("{}", mach);
    }
}
