use core::ops::Deref;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use itertools::{Itertools, enumerate};
use petgraph::Graph;

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::*;

pub type Deadcode = FunctionPass<Repeat<DeadcodeInner>>;

#[derive(Default, Clone, Copy, Debug)]
pub struct DeadcodeInner {}

impl DeadcodeInner {
    fn collect_necessary_instructions(
        bid: BlockId,
        code: &mut Block,
        init_sets: &mut HashMap<BlockId, HashSet<usize>>,
    ) {
        let collect =
            |init_sets: &mut HashMap<BlockId, HashSet<usize>>, bid: BlockId, iid: usize| {
                let _ = init_sets
                    .entry(bid)
                    .or_insert_with(Default::default)
                    .insert(iid);
            };
        code.exit.walk_jump_args(|arg| {
            for op in &arg.args {
                if let Some((reg, _)) = op.get_register()
                    && let RegisterId::Temp { iid, bid } = reg
                {
                    collect(init_sets, *bid, *iid);
                }
            }
        });
        if let Some(op) = code.exit.op()
            && let Some((reg, _)) = op.get_register()
            && let RegisterId::Temp { iid, bid } = reg
        {
            collect(init_sets, *bid, *iid);
        }
        for (idx, insn) in code.instructions.iter().enumerate() {
            match insn.inner() {
                Instruction::Store { .. }
                | Instruction::Load { .. }
                | Instruction::Call { .. }
                | Instruction::GetElementPtr { .. } => collect(init_sets, bid, idx),
                _ => {}
            }
        }
    }

    fn propagate_necessary_instructions(
        code: &mut FunctionDefinition,
        init_sets: &HashMap<BlockId, HashSet<usize>>,
    ) -> HashMap<BlockId, Vec<usize>> {
        let mut queue = vec![];
        for (bid, instruction_idxs) in init_sets {
            for idx in instruction_idxs {
                queue.push((*bid, *idx));
            }
        }

        let mut visited = HashMap::new();
        for (bid, block) in &code.blocks {
            let _ = visited.insert(*bid, vec![false; block.instructions.len()]);
        }

        let mut try_enqueue = |queue: &mut Vec<(BlockId, usize)>,
                               visited: &mut HashMap<BlockId, Vec<bool>>,
                               value: &Operand| {
            if !value.dtype().is_unit()
                && let Some((bid, iid)) = value.get_temp()
                && !visited[bid][*iid]
            {
                queue.push((*bid, *iid));
                return true;
            }
            false
        };

        while !queue.is_empty() {
            let (bid, idx) = queue.pop().unwrap();
            let block_visited = visited.get_mut(&bid).unwrap();
            if idx > block_visited.len() {
                panic!("{}-{}", bid, idx);
            }
            visited.get_mut(&bid).unwrap()[idx] = true;
            let block = code.blocks.get_mut(&bid).unwrap();

            block.instructions[idx].inner_mut().visit_ops_mut(|value| {
                let _ = try_enqueue(&mut queue, &mut visited, value);
            });
        }
        visited
            .into_iter()
            .map(|(k, v)| {
                (
                    k,
                    v.into_iter()
                        .enumerate()
                        .filter_map(|(idx, visited)| if visited { Some(idx) } else { None })
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<HashMap<_, _>>()
    }
}

impl Optimize<FunctionDefinition> for DeadcodeInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let mut used_allocs = HashSet::new();

        // for each block, the essential instruction before backward analysis
        let mut init_sets = HashMap::new();
        for (&bid, block) in code.blocks.iter_mut() {
            let _ = Self::collect_necessary_instructions(bid, block, &mut init_sets);
        }

        // necessary instructions for each block
        let necessary_insns = Self::propagate_necessary_instructions(code, &init_sets);
        // dbg!(&necessary_insns);

        // necessary allocs for the function
        for (bid, necess_insns) in &necessary_insns {
            let block = code.blocks.get(bid).unwrap();
            for inst in necess_insns {
                match block.instructions[*inst].inner() {
                    Instruction::Store { ptr, .. }
                    | Instruction::Load { ptr }
                    | Instruction::GetElementPtr { ptr, .. } => {
                        if let Some(aid) = ptr.get_alloc() {
                            let _ = used_allocs.insert(*aid);
                        }
                    }
                    _ => {}
                }
            }
        }

        // fix allocations
        // create a map from old to new alloc
        let mut old_allocs_to_new = HashMap::new();
        if used_allocs.len() != code.allocations.len() {
            changed = true;
            let mut new_allocs = vec![];
            for (idx, val) in code.allocations.iter().enumerate() {
                if used_allocs.contains(&idx) {
                    let _ = old_allocs_to_new.insert(idx, new_allocs.len());
                    new_allocs.push(val.clone());
                }
            }
            code.allocations = new_allocs;
        } else {
            old_allocs_to_new = (0..code.allocations.len())
                .map(|x| (x, x))
                .collect::<HashMap<_, _>>();
        }

        // bid -> (old inst idx -> new inst idx)
        let mut old_inst_to_new_all_blocks = HashMap::new();

        let mut update_op_if_is_temp =
            |op: &mut Operand, m: &HashMap<BlockId, HashMap<usize, usize>>| {
                if let Some((bid, iid)) = op.get_temp_mut() {
                    let inst_map: &HashMap<usize, usize> = m.get(bid).unwrap();
                    match inst_map.get(iid) {
                        Some(&new) => {
                            // println!("set {} {} to be {}", bid, iid, new);
                            *iid = new;
                        }
                        // it's the source of dataflow, no predecessor
                        None => {}
                    }
                }
            };

        // topographical traverse
        // make sure that data dependency across BB is also counted
        let mut visited = HashSet::new();
        let mut queue = VecDeque::from([code.bid_init]);
        while !queue.is_empty() {
            let bid = queue.pop_front().unwrap();
            if !visited.insert(bid) {
                continue;
            }

            let mut block = code.blocks.get_mut(&bid).unwrap();
            let mut necess_insns = necessary_insns.get(&bid).unwrap();
            let mut old_inst_to_new = necess_insns
                .iter()
                .enumerate()
                .map(|(idx, &inst_idx)| (inst_idx, idx))
                .collect::<HashMap<_, _>>();
            let _ = old_inst_to_new_all_blocks.insert(bid, old_inst_to_new);

            for (idx, inst_idx) in necess_insns.iter().enumerate() {
                let offset = *inst_idx - idx;
                let inst = block.instructions[*inst_idx].inner_mut();
                inst.visit_ops_mut(|op| {
                    update_op_if_is_temp(op, &old_inst_to_new_all_blocks);
                });
                inst.visit_ops_mut(|op| {
                    if let Some(aid) = op.get_alloc_mut() {
                        *aid = *old_allocs_to_new.get(aid).unwrap();
                    }
                });
                inst.visit_ops_mut(|op| {
                    if op.dtype().is_unit() {
                        *op = Operand::constant(Constant::Unit);
                    }
                });
            }

            block.exit.visit_op(|op| {
                update_op_if_is_temp(op, &old_inst_to_new_all_blocks);
            });
            block.exit.walk_jump_args_mut(|arg| {
                for op in &mut arg.args {
                    update_op_if_is_temp(op, &old_inst_to_new_all_blocks);
                }
            });

            let mut nexts = vec![];
            block.exit.walk_jump_args_mut(|arg| nexts.push(arg.bid));
            nexts.dedup();
            for next in nexts {
                queue.push_back(next);
            }
        }

        // fix instruction in each block
        for (bid, block) in code.blocks.iter_mut() {
            let necess_insn = necessary_insns.get(bid).unwrap();
            if necess_insn.len() != block.instructions.len() {
                changed = true;
            }
            block.instructions = necess_insn
                .iter()
                .map(|idx| block.instructions[*idx].clone())
                .collect::<Vec<_>>();
        }

        // now we have finished analyse of instructions
        // time to handle useless phinodes

        // 1. collect all useful phinodes
        //    the bid_init should be treated specially, since the argument of the function
        //    is always useful
        let mut useful_phinodes: HashMap<BlockId, BTreeSet<usize>> = HashMap::new();
        let _ = useful_phinodes.insert(
            code.bid_init,
            BTreeSet::from_iter((0..code.blocks[&code.bid_init].phinodes.len()).into_iter()),
        );
        for (bid, block) in code
            .blocks
            .iter_mut()
            .filter(|(bid, _)| **bid != code.bid_init)
        {
            let _ = useful_phinodes.insert(*bid, Default::default());
            let mut visitor = |op: &mut Operand| {
                if let Some((bid, aid)) = op.get_arg() {
                    let _ = useful_phinodes
                        .entry(*bid)
                        .or_insert_with(Default::default)
                        .insert(*aid);
                }
            };
            for insn in &mut block.instructions {
                let insn = insn.inner_mut();
                insn.visit_ops_mut(&mut visitor);
            }
            block.exit.visit_op(&mut visitor);
            block.exit.walk_jump_args_mut(|arg| {
                for op in &mut arg.args {
                    visitor(op);
                }
            });
        }

        // 2. from old phinode index to new index map
        let mut useful_phinodes_map = useful_phinodes
            .iter()
            .map(|(k, v)| {
                let value = v
                    .iter()
                    .enumerate()
                    .map(|(idx, &phinode_idx)| (phinode_idx, idx))
                    .collect::<HashMap<_, _>>();
                (*k, value)
            })
            .collect::<HashMap<_, _>>();

        // 3. fix jump args that use the useless phinodes
        for (bid, block) in code.blocks.iter_mut() {
            block.exit.walk_jump_args_mut(|arg| {
                let jump_target_phinodes = useful_phinodes_map.get(&arg.bid).unwrap();
                let used = arg
                    .args
                    .iter()
                    .enumerate()
                    .filter(|(idx, _)| jump_target_phinodes.contains_key(idx))
                    .filter_map(|(_, op)| {
                        if let Some((bid, aid)) = op.get_arg() {
                            let useful_map = useful_phinodes_map.get(&bid).unwrap();
                            useful_map.get(aid).map(|new_idx| {
                                let mut new_op = op.clone();
                                new_op.set_arg(|_, aid| *aid = *new_idx);
                                new_op
                            })
                        } else {
                            Some(op.clone())
                        }
                    })
                    .collect::<Vec<_>>();
                arg.args = used;
            });
        }

        // 4. fix phinodes declaration in each block
        for (bid, block) in code.blocks.iter_mut() {
            let Some(useful) = useful_phinodes.get(bid) else {
                continue;
            };
            block.phinodes = block
                .phinodes
                .iter()
                .enumerate()
                .filter_map(|(idx, phi)| {
                    if useful.contains(&idx) {
                        Some(phi.clone())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
        }

        // 5. fix instructions that uses the phinodes
        for (bid, block) in code.blocks.iter_mut() {
            for insn in &mut block.instructions {
                let insn = insn.inner_mut();
                insn.visit_ops_mut(|op| {
                    if let Some((bid, aid)) = op.get_arg_mut() {
                        *aid = useful_phinodes_map[bid][aid];
                    }
                });
            }
        }

        // dbg!(old_inst_to_new_all_blocks);
        // print_all(code);

        changed
    }
}

fn print_all(code: &mut FunctionDefinition) {
    println!("=====start");
    for (bid, block) in &code.blocks {
        println!("block b{bid}:");
        for (idx, insn) in block.instructions.iter().enumerate() {
            println!("  %{bid}:i{idx}:{} = {}", insn.dtype(), insn);
        }
        println!("{}", block.exit);
    }
    println!("end=====");
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{Deadcode, FunctionPass, test_opt};

    #[test]
    fn t1() {
        test_opt(
            &Path::new("examples/deadcode/deadcode.input.ir"),
            &Path::new("examples/deadcode/deadcode.output.ir"),
            &mut Deadcode::default(),
        );
    }

    #[test]
    fn test_basic() {
        test_opt(
            &Path::new("examples/ir2/array4.ir"),
            &Path::new("examples/ir3/array4.ir"),
            &mut Deadcode::default(),
        );
    }
}
