use core::ops::{Deref, DerefMut};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::worklist::WorkList;
use crate::opt::*;

fn find_all_promotable_allocs(code: &FunctionDefinition) -> Vec<usize> {
    let mut unusable: HashSet<usize> = HashSet::new();

    for block in code.blocks.values() {
        for insn in &block.instructions {
            // if it's not a pure load/store of an alloc
            // then it's not promotable
            if !matches!(insn.inner(), Instruction::Load { .. })
                && !matches!(insn.inner(), Instruction::Store { .. })
            {
                insn.visit_ops(|op| {
                    if let Some((reg, _)) = op.get_register()
                        && let RegisterId::Local { aid } = reg
                    {
                        let _ = unusable.insert(*aid);
                    }
                });
            }
            if let Instruction::Store { ptr, value } = insn.inner()
                && let Some((reg, _)) = value.get_register()
                && let RegisterId::Local { aid } = reg
            {
                let _ = unusable.insert(*aid);
            }
        }
    }

    (0..code.allocations.len())
        .into_iter()
        .filter(|alloc| !unusable.contains(alloc))
        .collect::<Vec<_>>()
}

fn find_stores_for_alloc(code: &FunctionDefinition, alloc: usize) -> HashSet<BlockId> {
    let mut res = HashSet::new();

    for (&bid, block) in &code.blocks {
        for insn in &block.instructions {
            match insn.inner() {
                Instruction::Store { ptr, value } => {
                    if let Some((reg, _)) = ptr.get_register()
                        && let RegisterId::Local { aid } = reg
                        && *aid == alloc
                    {
                        let _ = res.insert(bid);
                        break;
                    }
                }
                _ => {}
            }
        }
    }

    res
}

#[derive(Debug, Clone)]
struct DefUse {
    alloc: usize,
    // for each block, (idx of instruction idx within block that defines, Op)
    defs: HashMap<BlockId, BTreeMap<usize, Operand>>,
    // for each block, list of (instruction idx within block that uses, corresponding def idx)
    uses: HashMap<BlockId, Vec<(usize, Option<usize>)>>,
}

impl DefUse {
    fn build(code: &mut FunctionDefinition, alloc: usize) -> Self {
        let mut defs: HashMap<BlockId, BTreeMap<usize, Operand>> = HashMap::new();
        let mut uses: HashMap<BlockId, Vec<(usize, Option<usize>)>> = HashMap::new();

        for (&bid, block) in &code.blocks {
            for (idx, insn) in block.instructions.iter().enumerate() {
                match insn.inner() {
                    Instruction::Store { ptr, value } => {
                        if let Some((reg, _)) = ptr.get_register()
                            && let RegisterId::Local { aid } = reg
                            && *aid == alloc
                        {
                            let _ = defs.entry(bid).or_default().insert(idx, value.clone());
                        }
                    }
                    Instruction::GetElementPtr { ptr, .. } | Instruction::Load { ptr } => {
                        if let Some((reg, _)) = ptr.get_register()
                            && let RegisterId::Local { aid } = reg
                            && *aid == alloc
                        {
                            uses.entry(bid)
                                .or_default()
                                .push((idx, defs.entry(bid).or_default().keys().last().cloned()));
                        }
                    }
                    _ => {}
                }
            }
        }

        Self { alloc, defs, uses }
    }

    fn update_code(&self, code: &mut FunctionDefinition) {
        for (bid, def) in &self.defs {
            let block = code.blocks.get_mut(&bid).unwrap();
            for &idx in def.keys() {
                *block.instructions[idx].inner_mut() = Instruction::Nop;
            }
        }

        for (bid, uses) in &self.uses {
            let block = code.blocks.get_mut(&bid).unwrap();
            for &(idx, _) in uses {
                *block.instructions[idx].inner_mut() = Instruction::Nop;
            }

            for insn in &mut block.instructions {
                let insn = insn.inner_mut();
                insn.visit_ops_mut(|op| {
                    if let Some((reg, _)) = op.get_register()
                        && let RegisterId::Temp { bid, iid } = reg
                    {
                        // if let Some(replace) = self.uses.get(bid).and_then(|m| m.get(iid)) {
                        // *op = replace.clone();
                        // }
                    }
                });
            }
        }
    }
}

pub type Mem2reg = FunctionPass<Mem2regInner>;

#[derive(Default, Clone, Copy, Debug)]
pub struct Mem2regInner {}

impl Optimize<FunctionDefinition> for Mem2regInner {
    /// for each alloc:
    ///     1. collect all def(store) of alloc
    ///     2. calculate the blocks to insert phinode by dominance frontier
    ///     3. traverse all blocks in dominance tree preorder, maintain a stack
    ///         a. push phinode value to stack if needed
    ///         b. replace load with top value of the stack, push value of store inst to stack
    ///         a. fill phinodes of successors & undo all stack operations
    ///
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let (cfg, bid_to_idx) = build_cfg(code);
        let (df, dom_tree, dom) = dominance_frontiers(&cfg, bid_to_idx[&code.bid_init]);

        struct AllocInfo {
            dtype: Dtype,
            name: Option<String>,
            phi_blocks: HashSet<BlockId>,
            finals: HashMap<BlockId, Operand>,
            uses: HashMap<BlockId, HashMap<usize, Operand>>,
        }

        let mut alloc_infos: BTreeMap<usize, AllocInfo> = BTreeMap::new();
        for alloc in find_all_promotable_allocs(code) {
            let dtype = code.allocations[alloc].inner().clone();
            let name = code.allocations[alloc].name().cloned();
            let defs = find_stores_for_alloc(code, alloc);
            let phi_blocks = phi_insert_at(defs, &df);

            let _ = alloc_infos.insert(
                alloc,
                AllocInfo {
                    dtype,
                    name,
                    phi_blocks,
                    finals: HashMap::new(),
                    uses: HashMap::new(),
                },
            );
        }

        // 2. one stack per alloc
        let mut stacks: HashMap<usize, Vec<Operand>> =
            alloc_infos.keys().map(|&a| (a, vec![])).collect();

        // 3. traverse dom tree
        let mut visited = Default::default();
        let bid_init = code.bid_init;

        visit_dom_tree(&dom_tree, &mut visited, bid_init, &mut |cur| {
            let node = bid_to_idx[&cur];
            let block = code.blocks.get_mut(&cur).unwrap();


            // intialize stack for current block
            for (&alloc, info) in alloc_infos.iter_mut() {
                let stack = stacks.get_mut(&alloc).unwrap();

                if let Some(d) = dom.immediate_dominator(node) {
                    if let Some(val) = info.finals.get(&cfg[d]) {
                        stack.push(val.clone());
                    }
                }

                if info.phi_blocks.contains(&cur) {
                    let phi_op = Operand::register(
                        RegisterId::Arg {
                            bid: cur,
                            aid: block.phinodes.len(),
                        },
                        info.dtype.clone(),
                    );
                    block
                        .phinodes
                        .push(Named::new(info.name.clone(), info.dtype.clone()));
                    stack.push(phi_op);
                }
            }

            // visit all instructions
            for (idx, insn) in block.instructions.iter_mut().enumerate() {
                insn.inner_mut().visit_ops_mut(|op| {
                    for info in alloc_infos.values() {
                        if let Some((reg, _)) = op.get_register()
                            && let RegisterId::Temp { bid, iid } = reg
                            && let Some(r) = info.uses.get(bid).and_then(|m| m.get(iid))
                        {
                            *op = r.clone();
                        }
                    }
                });

                match insn.inner_mut() {
                    Instruction::Store { ptr, value } => {
                        if let Some((reg, _)) = ptr.get_register()
                            && let RegisterId::Local { aid } = reg
                            && let Some(stack) = stacks.get_mut(aid)
                        {
                            stack.push(value.clone());
                            *insn.inner_mut() = Instruction::Nop;
                            changed = true;
                        }
                    }
                    Instruction::Load { ptr } => {
                        if let Some((reg, _)) = ptr.get_register()
                            && let RegisterId::Local { aid } = reg
                            && let Some(stack) = stacks.get(aid)
                        {
                            let op = stack
                                .last()
                                .cloned()
                                .unwrap_or(Operand::undef(alloc_infos[aid].dtype.clone()));
                            let _ = alloc_infos
                                .get_mut(aid)
                                .unwrap()
                                .uses
                                .entry(cur)
                                .or_default()
                                .insert(idx, op);
                            *insn.inner_mut() = Instruction::Nop;
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }

            // handle block exit
            for (&alloc, info) in alloc_infos.iter_mut() {
                let stack = stacks.get_mut(&alloc).unwrap();
                let last = match stack.pop() {
                    Some(op) => op,
                    None if cur == code.bid_init => Operand::undef(info.dtype.clone()),
                    _ => panic!(),
                };
                let _ = info.finals.insert(cur, last.clone());

                block.exit.visit_op(|op| {
                    if let Some((reg, _)) = op.get_register()
                        && let RegisterId::Temp { bid, iid } = reg
                        && let Some(replace) = info.uses.get(bid).and_then(|m| m.get(iid))
                    {
                        *op = replace.clone();
                    }
                });

                block.exit.walk_jump_args_mut(|arg| {
                    if info.phi_blocks.contains(&arg.bid) {
                        arg.args.push(last.clone());
                    }
                });
            }
        });

        changed
    }
}

fn visit_dom_tree(
    dom_tree: &HashMap<BlockId, Vec<BlockId>>,
    visited: &mut HashSet<BlockId>,
    cur: BlockId,
    visitor: &mut impl FnMut(BlockId),
) {
    if !visited.insert(cur) {
        return;
    }

    visitor(cur);

    if let Some(children) = dom_tree.get(&cur) {
        for child in children {
            visit_dom_tree(dom_tree, visited, *child, visitor);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{FunctionPass, Mem2reg, test_opt};

    #[test]
    fn t1() {
        // test_opt(
        //     &Path::new("examples/mem2reg/temp.input.ir"),
        //     &Path::new("examples/mem2reg/temp.output.ir"),
        //     &mut Mem2reg::default(),
        // );

        test_opt(
            &Path::new("examples/mem2reg/mem2reg.input.ir"),
            &Path::new("examples/mem2reg/mem2reg.output.ir"),
            &mut Mem2reg::default(),
        );
    }

    #[test]
    fn test_basic() {
        test_opt(
            &Path::new("examples/ir1/typedef.ir"),
            &Path::new("examples/ir2/typedef.ir"),
            &mut Mem2reg::default(),
        );
    }
}
