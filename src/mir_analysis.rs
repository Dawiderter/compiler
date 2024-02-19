use std::{collections::HashSet, fmt::Display, ops::Range};

use slotmap::{new_key_type, SecondaryMap, SlotMap};

use crate::mir::{
    CondOp, Id, MathOp, MirBuilder, MirInstr, MirLabel, MirProcedure, MirVar, MirVarInfo,
    MirVarType,
};

new_key_type! { pub struct BlockId; }

#[derive(Debug, Default, Clone)]
pub struct BasicBlock {
    prev: HashSet<BlockId>,
    next: HashSet<BlockId>,
    instr: Vec<MirInstr>,
}

#[derive(Debug, Clone, Default)]
pub struct ControlFlowGraph {
    blocks: SlotMap<BlockId, BasicBlock>,
    block_seq: Vec<BlockId>,
    labels: SecondaryMap<MirLabel, BlockId>,
}

impl ControlFlowGraph {
    pub fn construct(proc: &[MirInstr]) -> Self {
        let mut graph = Self {
            blocks: SlotMap::with_key(),
            labels: SecondaryMap::new(),
            block_seq: Vec::new(),
        };

        let mut save_block = |block: &mut BasicBlock, label: &mut Option<MirLabel>| {
            let block = std::mem::take(block);
            let block_id = graph.blocks.insert(block);
            if let Some(label_id) = label.take() {
                graph.labels.insert(label_id, block_id);
            }
            graph.block_seq.push(block_id);
        };

        let mut current_block = BasicBlock::default();
        let mut last_label = None;
        for instr in proc {
            if let MirInstr::Label(label) = instr {
                if !current_block.instr.is_empty() {
                    save_block(&mut current_block, &mut last_label);
                }
                last_label = Some(*label);
            }

            current_block.instr.push(instr.to_owned());

            if instr.is_terminator() {
                save_block(&mut current_block, &mut last_label);
            }
        }

        debug_assert!(current_block.instr.is_empty());

        for i in 0..graph.block_seq.len() {
            let from = graph.block_seq[i];
            let last_instr = *graph.blocks[from].instr.last().unwrap();
            // Kończy się bezwarunkowym jumpem -> przejście tylko do danego labela
            // Warunkowy jump -> przejście do danego labela i do następnego bloku
            // Brak jumpa -> przejście do następnego bloku

            match last_instr {
                MirInstr::Jump(label, None) => {
                    let to = graph.labels[label];
                    graph.blocks[from].next.insert(to);
                    graph.blocks[to].prev.insert(from);
                }
                MirInstr::JumpCond(label, _, _, _) => {
                    let to = graph.labels[label];
                    graph.blocks[from].next.insert(to);
                    graph.blocks[to].prev.insert(from);
                    if i + 1 < graph.block_seq.len() {
                        let to = graph.block_seq[i + 1];
                        graph.blocks[from].next.insert(to);
                        graph.blocks[to].prev.insert(from);
                    }
                }
                _ => {
                    if i + 1 < graph.block_seq.len() {
                        let to = graph.block_seq[i + 1];
                        graph.blocks[from].next.insert(to);
                        graph.blocks[to].prev.insert(from);
                    }
                }
            }
        }
        graph
    }
}

#[derive(Debug, Clone, Default)]
pub struct BlockLiveness {
    live_in: HashSet<MirVar>,
    live_out: HashSet<MirVar>,
    defs: HashSet<MirVar>,
    reads: HashSet<MirVar>,
}

#[derive(Debug, Clone, Default)]
pub struct LivenessGraph {
    blocks: SecondaryMap<BlockId, BlockLiveness>,
}

impl LivenessGraph {
    pub fn construct(cfg: &ControlFlowGraph) -> Self {
        let mut liveness = LivenessGraph::default();

        for (block_id, block) in &cfg.blocks {
            let mut live_block = BlockLiveness::default();
            for instr in &block.instr {
                let read = instr.uses();
                for read_var in read {
                    if !live_block.defs.contains(&read_var) {
                        live_block.reads.insert(read_var);
                    }
                }

                let writes = instr.defs();
                if let Some(write_var) = writes {
                    live_block.defs.insert(write_var);
                }
            }
            liveness.blocks.insert(block_id, live_block);
        }

        let keys = cfg.blocks.keys().collect::<Vec<_>>();

        // Reguła 2. Uzupełnij live_in o zmienne, które są czytane w tym bloku
        for &block_id in keys.iter() {
            let block = &mut liveness.blocks[block_id];
            for &read in &block.reads {
                block.live_in.insert(read);
            }
        }

        let mut has_improved = true;
        while has_improved {
            has_improved = false;

            for &block_id in keys.iter().rev() {
                let mut curr_block = std::mem::take(&mut liveness.blocks[block_id]);
                // Reguła 1. Wszystkie live_in zmienne sukcesorów są przepisane do live_out
                for &succ in &cfg.blocks[block_id].next {
                    for &live_in in &liveness.blocks[succ].live_in {
                        if !curr_block.live_out.contains(&live_in) {
                            curr_block.live_out.insert(live_in);
                            has_improved = true;
                        }
                    }
                }
                // Reguła 4. Przepisujemy live_out do live_in, jeżeli nie ma write
                for &live_out in &curr_block.live_out {
                    if !curr_block.defs.contains(&live_out)
                        && !curr_block.live_in.contains(&live_out)
                    {
                        curr_block.live_in.insert(live_out);
                        has_improved = true;
                    }
                }
                liveness.blocks[block_id] = curr_block;
            }
        }

        liveness
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Register(u8);

impl Register {
    pub const A: Self = Register(0);
    pub const B: Self = Register(1);
    pub const C: Self = Register(2);
    pub const D: Self = Register(3);
    pub const E: Self = Register(4);
    pub const F: Self = Register(5);
    pub const G: Self = Register(6);
    pub const H: Self = Register(7);
}

new_key_type! { pub struct MemorySlot; }

#[derive(Debug, Clone, Copy)]
pub enum SpillInfo {
    Spilled(MemorySlot),
    Reg(Register),
}

new_key_type! { pub struct NodeId; }

#[derive(Debug, Clone)]
pub struct Node {
    neigh: HashSet<MirVar>,
    cant: Range<u8>,
    curr_spill: Option<SpillInfo>,
}

#[derive(Debug, Clone, Default)]
pub struct InterferenceGraph {
    pub already_set: SecondaryMap<MirVar, SpillInfo>,
    pub variables: SlotMap<MirVar, MirVarInfo>,
    pub memory: SlotMap<MemorySlot, u64>,
    pub used_in_proc: SecondaryMap<MirProcedure, Range<u8>>,
    pub graph: SecondaryMap<MirVar, Node>,
    pub liveness: LivenessGraph,
    pub cfg: ControlFlowGraph,
}

impl InterferenceGraph {
    pub fn new(liveness: LivenessGraph, cfg: ControlFlowGraph) -> Self {
        Self {
            liveness,
            cfg,
            ..Default::default()
        }
    }

    pub fn allocate(&mut self, proc: MirProcedure) {
        self.rebuild();
        let (stack, rest_graph) = self.simplify();
        self.color(stack, rest_graph);
        self.save(proc);
    }

    fn new_spilled_mem(&mut self) -> MemorySlot {
        self.memory.insert(1)
    }

    fn used_regs(&self, instr: &MirInstr) -> Range<u8> {
        match instr {
            MirInstr::Load(_, _) => 0..2,
            MirInstr::Store(_, _) => 0..2,
            MirInstr::Assign(_, _) => 0..2,
            MirInstr::AssignExpr(_, _, MathOp::Add, _) => 0..2,
            MirInstr::AssignExpr(_, _, MathOp::Sub, _) => 0..2,
            MirInstr::AssignExpr(_, _, MathOp::Div, _) => 0..6,
            MirInstr::AssignExpr(_, _, MathOp::Rem, _) => 0..6,
            MirInstr::AssignExpr(_, _, MathOp::Mul, _) => 0..5,
            MirInstr::LoadAddress(_, _) => 0..2,
            MirInstr::Jump(_, None) => 0..0,
            MirInstr::Jump(_, Some(proc)) => self.used_in_proc[*proc].clone(),
            MirInstr::JumpCond(_, _, CondOp::IsEqual, _) => 0..3,
            MirInstr::JumpCond(_, _, CondOp::IsNotEqual, _) => 0..3,
            MirInstr::JumpCond(_, _, CondOp::IsLess, _) => 0..2,
            MirInstr::JumpCond(_, _, CondOp::IsLessEqual, _) => 0..2,
            MirInstr::Strk(_) => 0..2,
            MirInstr::JumpReturn(_) => 0..2,
            MirInstr::Read(_) => 0..2,
            MirInstr::Write(_) => 0..2,
            MirInstr::Label(_) => 0..0,
            MirInstr::Halt => 0..0,
            MirInstr::Noop => 0..0,
            MirInstr::NoopRead(_) => 0..0,
        }
    }

    fn insert_new_node(
        vars: &SlotMap<MirVar, MirVarInfo>,
        memory: &mut SlotMap<MemorySlot, u64>,
        graph: &mut SecondaryMap<MirVar, Node>,
        var: MirVar,
    ) {
        if !graph.contains_key(var) {
            let node = if let MirVarType::TableLocal(n) = vars[var].typ {
                let mem = memory.insert(n);
                Node {
                    curr_spill: Some(SpillInfo::Spilled(mem)),
                    cant: 0..0,
                    neigh: HashSet::new(),
                }
            } else {
                Node {
                    curr_spill: None,
                    cant: 0..0,
                    neigh: HashSet::new(),
                }
            };
            graph.insert(var, node);
        }
    }

    fn insert_connection(graph: &mut SecondaryMap<MirVar, Node>, x: MirVar, y: MirVar) {
        graph[x].neigh.insert(y);
        graph[y].neigh.insert(x);
    }

    fn insert_connections(graph: &mut SecondaryMap<MirVar, Node>, set: &HashSet<MirVar>) {
        for &x in set {
            for &y in set {
                if x != y {
                    Self::insert_connection(graph, x, y);
                }
            }
        }
    }

    fn insert_regs(graph: &mut SecondaryMap<MirVar, Node>, set: &HashSet<MirVar>, regs: Range<u8>) {
        for &x in set {
            let node = &mut graph[x];
            node.cant = (regs.start.min(node.cant.start))..(regs.end.max(node.cant.end));
        }
    }

    fn rebuild(&mut self) {
        self.graph = SecondaryMap::new();
        for (var, spill) in &self.already_set {
            self.graph.insert(
                var,
                Node {
                    curr_spill: Some(*spill),
                    cant: 0..0,
                    neigh: HashSet::new(),
                },
            );
        }

        for (block_id, block) in &self.cfg.blocks {
            let mut live = self.liveness.blocks[block_id].live_out.clone();
            for &var in &live {
                Self::insert_new_node(&self.variables, &mut self.memory, &mut self.graph, var);
            }

            for instr in block.instr.iter().rev() {
                let regs = self.used_regs(instr);

                let defs = instr.defs();
                if let Some(var) = defs {
                    live.remove(&var);
                    Self::insert_new_node(&self.variables, &mut self.memory, &mut self.graph, var);
                }

                let reads = instr.uses();
                for read in reads {
                    live.insert(read);
                    Self::insert_new_node(&self.variables, &mut self.memory, &mut self.graph, read);
                }

                Self::insert_connections(&mut self.graph, &live);
                Self::insert_regs(&mut self.graph, &live, regs);
            }
        }
    }

    fn simplify(&mut self) -> (Vec<MirVar>, SecondaryMap<MirVar, Node>) {
        let mut stack = Vec::new();

        let mut s_gr = self.graph.clone();

        loop {
            let min_neighbour = s_gr
                .iter()
                .filter(|(_, n)| n.curr_spill.is_none())
                .min_by_key(|(_, n)| n.neigh.len() + n.cant.len());
            let Some((var, node)) = min_neighbour else { break; };

            if node.neigh.len() + node.cant.len() >= 8 {
                let (to_spill, _) = s_gr
                    .iter()
                    .filter(|(_, n)| n.curr_spill.is_none())
                    .max_by_key(|(_, n)| n.neigh.len() + n.cant.len())
                    .unwrap();
                let node = s_gr.remove(to_spill).unwrap();
                for neigh in node.neigh {
                    s_gr[neigh].neigh.remove(&to_spill);
                }
                stack.push(to_spill);
            } else {
                let node = s_gr.remove(var).unwrap();
                for neigh in node.neigh {
                    s_gr[neigh].neigh.remove(&var);
                }
                stack.push(var);
            }
        }

        (stack, s_gr)
    }

    fn color(&mut self, mut stack: Vec<MirVar>, mut gr: SecondaryMap<MirVar, Node>) {
        while let Some(var) = stack.pop() {
            let mut node = self.graph[var].clone();
            node.neigh.retain(|&n| gr.contains_key(n));

            for &neigh in &node.neigh {
                gr[neigh].neigh.insert(var);
            }

            // Zmienna jeszcze nie ma przydzielonego miejsca
            if node.curr_spill.is_none() {
                let mut available_regs = [true; 8];
                for &neigh in &node.neigh {
                    let n_curr_spill = gr[neigh].curr_spill.unwrap();
                    if let SpillInfo::Reg(Register(i)) = n_curr_spill {
                        available_regs[i as usize] = false;
                    }
                }
                for cant_reg in node.cant.clone() {
                    available_regs[cant_reg as usize] = false;
                }

                let first_good = available_regs.into_iter().enumerate().find(|&(_, a)| a);

                if let Some((good, _)) = first_good {
                    node.curr_spill = Some(SpillInfo::Reg(Register(good as u8)));
                } else {
                    node.curr_spill = Some(SpillInfo::Spilled(self.new_spilled_mem()))
                }
            }

            gr.insert(var, node);
        }

        self.graph = gr;
    }

    fn save(&mut self, proc: MirProcedure) {
        let mut used_range = 0..0;
        for (var, node) in &self.graph {
            if let Some(SpillInfo::Reg(Register(reg))) = node.curr_spill {
                used_range = 0..(used_range.end.max(reg + 1).max(node.cant.end));
            }
            self.already_set.insert(var, node.curr_spill.unwrap());
        }
        self.used_in_proc.insert(proc, used_range);
    }
}

pub fn optimize_mir(mir: &MirBuilder) -> InterferenceGraph {
    let mut rig = InterferenceGraph {
        variables: mir.variables.clone(),
        ..Default::default()
    };

    for (i, info) in &mir.procedures {
        let instr = &info.instr;
        let cfg = ControlFlowGraph::construct(instr);
        let liveness = LivenessGraph::construct(&cfg);

        rig = InterferenceGraph {
            liveness,
            cfg,
            ..rig
        };

        rig.allocate(i);
    }

    rig
}

pub fn flatten(mir: &MirBuilder) -> Vec<MirInstr> {
    let mut acc = Vec::new();

    acc.extend_from_slice(&mir.procedures[mir.main].instr);

    for (i, proc) in &mir.procedures {
        if i != mir.main {
            acc.extend_from_slice(&proc.instr);
        }
    }

    acc
}

impl Display for BasicBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for instr in &self.instr {
            writeln!(f, "{}", instr)?;
        }
        Ok(())
    }
}

impl Display for BlockLiveness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Live in:")?;
        for i in &self.live_in {
            write!(f, " {}", i)?;
        }
        writeln!(f)?;
        write!(f, "Live out:")?;
        for i in &self.live_out {
            write!(f, " {}", i)?;
        }
        writeln!(f)?;
        write!(f, "Uses:")?;
        for i in &self.reads {
            write!(f, " {}", i)?;
        }
        writeln!(f)?;
        write!(f, "Defs:")?;
        for i in &self.defs {
            write!(f, " {}", i)?;
        }
        writeln!(f)?;
        Ok(())
    }
}

impl Display for MemorySlot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.id())
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", (self.0 + b'a') as char)
    }
}

impl Display for SpillInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpillInfo::Spilled(mem) => write!(f, "[{}]", mem),
            SpillInfo::Reg(reg) => write!(f, "{}", reg),
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(i) = self.curr_spill {
            writeln!(f, "Spill: {}", i)?
        }
        writeln!(f, "Cant: {:?}", self.cant)?;
        writeln!(f, "Neighs: {}", self.neigh.len())?;
        Ok(())
    }
}

impl<'a> dot::Labeller<'a, BlockId, (BlockId, BlockId)> for ControlFlowGraph {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("control_flow_graph").unwrap()
    }

    fn node_id(&'a self, n: &BlockId) -> dot::Id<'a> {
        dot::Id::new(format!("Block_{}", n.id())).unwrap()
    }

    fn node_shape(&'a self, _node: &BlockId) -> Option<dot::LabelText<'a>> {
        Some(dot::LabelText::LabelStr("box".into()))
    }

    fn node_label(&'a self, n: &BlockId) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(format!("{}", self.blocks[*n]).into())
    }
}

impl<'a> dot::GraphWalk<'a, BlockId, (BlockId, BlockId)> for ControlFlowGraph {
    fn nodes(&'a self) -> dot::Nodes<'a, BlockId> {
        self.blocks.keys().collect()
    }

    fn edges(&'a self) -> dot::Edges<'a, (BlockId, BlockId)> {
        let mut edges = Vec::new();

        for (i, block) in &self.blocks {
            for &j in &block.next {
                edges.push((i, j));
            }
        }

        edges.into()
    }

    fn source(&'a self, edge: &(BlockId, BlockId)) -> BlockId {
        edge.0
    }

    fn target(&'a self, edge: &(BlockId, BlockId)) -> BlockId {
        edge.1
    }
}

impl<'a> dot::Labeller<'a, BlockId, (BlockId, BlockId)> for (ControlFlowGraph, LivenessGraph) {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("control_flow_graph").unwrap()
    }

    fn node_id(&'a self, n: &BlockId) -> dot::Id<'a> {
        dot::Id::new(format!("Block_{}", n.id())).unwrap()
    }

    fn node_shape(&'a self, _node: &BlockId) -> Option<dot::LabelText<'a>> {
        Some(dot::LabelText::LabelStr("box".into()))
    }

    fn node_label(&'a self, n: &BlockId) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(format!("{} {}", self.1.blocks[*n], self.0.blocks[*n]).into())
    }
}

impl<'a> dot::GraphWalk<'a, BlockId, (BlockId, BlockId)> for (ControlFlowGraph, LivenessGraph) {
    fn nodes(&'a self) -> dot::Nodes<'a, BlockId> {
        self.0.blocks.keys().collect()
    }

    fn edges(&'a self) -> dot::Edges<'a, (BlockId, BlockId)> {
        let mut edges = Vec::new();

        for (i, block) in &self.0.blocks {
            for &j in &block.next {
                edges.push((i, j));
            }
        }

        edges.into()
    }

    fn source(&'a self, edge: &(BlockId, BlockId)) -> BlockId {
        edge.0
    }

    fn target(&'a self, edge: &(BlockId, BlockId)) -> BlockId {
        edge.1
    }
}

impl<'a> dot::Labeller<'a, MirVar, (MirVar, MirVar)> for InterferenceGraph {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("interference_graph").unwrap()
    }

    fn node_id(&'a self, n: &MirVar) -> dot::Id<'a> {
        dot::Id::new(format!("n{}", n.id())).unwrap()
    }

    fn node_shape(&'a self, _node: &MirVar) -> Option<dot::LabelText<'a>> {
        Some(dot::LabelText::LabelStr("circle".into()))
    }

    fn node_label(&'a self, n: &MirVar) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(format!("{}\n{}", n, self.graph[*n]).into())
    }
}

impl<'a> dot::GraphWalk<'a, MirVar, (MirVar, MirVar)> for InterferenceGraph {
    fn nodes(&'a self) -> dot::Nodes<'a, MirVar> {
        self.graph.keys().collect()
    }

    fn edges(&'a self) -> dot::Edges<'a, (MirVar, MirVar)> {
        let mut edges = Vec::new();

        for (i, block) in &self.graph {
            for &j in &block.neigh {
                if i <= j {
                    edges.push((i, j));
                }
            }
        }

        edges.into()
    }

    fn source(&'a self, edge: &(MirVar, MirVar)) -> MirVar {
        edge.0
    }

    fn target(&'a self, edge: &(MirVar, MirVar)) -> MirVar {
        edge.1
    }
}

#[cfg(test)]
mod tests {
    use std::fs::File;

    use winnow::Parser;

    use crate::{ast::program, ast_analysis::optimize_ast, lexer::lex_str, mir::MirBuilder};

    use super::*;

    fn gen_mir() -> MirBuilder {
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
        MirBuilder::build_program(&prog)
    }

    #[test]
    fn construction_test() {
        let mir = gen_mir();

        eprintln!("{}", mir);

        let proc = mir.main;
        let instr = &mir.procedures[proc].instr;

        let graph = ControlFlowGraph::construct(instr);

        let liveness = LivenessGraph::construct(&graph);

        let mut f = File::create("test.dot").unwrap();
        dot::render(&(graph, liveness), &mut f).unwrap();
    }

    #[test]
    fn inference_test() {
        let mir = gen_mir();

        eprintln!("{}", mir);

        let proc = mir.main;
        let instr = &mir.procedures[proc].instr;

        let graph = ControlFlowGraph::construct(instr);

        let liveness = LivenessGraph::construct(&graph);

        let mut interference = InterferenceGraph::new(liveness, graph);

        interference.rebuild();

        let mut f = File::create("int1.dot").unwrap();
        dot::render_opts(&interference, &mut f, &[dot::RenderOption::NoArrows]).unwrap();

        let (stack, rest_graph) = interference.simplify();

        interference.color(stack, rest_graph);

        let mut f = File::create("int2.dot").unwrap();
        dot::render_opts(&interference, &mut f, &[dot::RenderOption::NoArrows]).unwrap();
    }
}
