use std::collections::{HashMap, HashSet, VecDeque};
use std::ops::Deref;

use itertools::izip;
use petgraph::prelude::*;
use serde::de;

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::*;

pub type SimplifyCfg = FunctionPass<
    Repeat<(
        SimplifyCfgConstProp,
        (SimplifyCfgReach, (SimplifyCfgMerge, SimplifyCfgEmpty)),
    )>,
>;

/// Simplifies block exits by propagating constants.
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgConstProp {}

/// Retains only those blocks that are reachable from the init.
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgReach {}

/// Merges two blocks if a block is pointed to only by another
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgMerge {}

/// Removes empty blocks
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgEmpty {}

impl Optimize<FunctionDefinition> for SimplifyCfgConstProp {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let graph = build_cfg(code);

        for (bid, block) in &mut code.blocks {
            let mut new_exit = None;
            match &block.exit {
                BlockExit::Jump { .. } => {}
                BlockExit::ConditionalJump {
                    condition,
                    arg_then,
                    arg_else,
                } => {
                    if let Some(c) = condition.get_constant() {
                        let arg = if arg_then.bid == arg_else.bid
                            || c.get_int().map(|x| x.0) == Some(1)
                        {
                            arg_then
                        } else {
                            arg_else
                        }
                        .clone();
                        new_exit = Some(BlockExit::Jump { arg });
                    }
                }
                BlockExit::Switch {
                    value,
                    default,
                    cases,
                } => {
                    if let Some(c) = value.get_constant() {
                        for arg in cases.iter() {
                            if arg.0.eq(c) {
                                new_exit = Some(BlockExit::Jump { arg: arg.1.clone() });
                            }
                        }
                        if new_exit.is_none() {
                            new_exit = Some(BlockExit::Jump {
                                arg: default.clone(),
                            });
                        }
                    }
                }
                _ => {}
            }
            if let Some(new_exit) = new_exit {
                block.exit = new_exit;
                changed = true;
            }
        }
        changed
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgReach {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let mut reachable = HashSet::new();
        let mut visited = HashSet::new();
        let mut queue = VecDeque::from([code.bid_init]);
        while !queue.is_empty() {
            let cur = queue.pop_front().unwrap();
            if !visited.insert(cur) {
                continue;
            }
            let _ = reachable.insert(cur);
            let block = code.blocks.get(&cur).unwrap();
            block.exit.walk_jump_args(|arg| {
                queue.push_back(arg.bid);
            });
        }

        if reachable.len() != code.blocks.len() {
            changed = true;
            code.blocks.retain(|bid, _| reachable.contains(bid));
        }

        changed
    }
}
fn merge_block_paths(pairs: Vec<(BlockId, BlockId)>) -> Vec<Vec<BlockId>> {
    let mut from_map: HashMap<BlockId, BlockId> = HashMap::new();
    let mut to_map: HashMap<BlockId, BlockId> = HashMap::new();

    for (from, to) in &pairs {
        let _ = from_map.insert(from.clone(), to.clone());
        let _ = to_map.insert(to.clone(), from.clone());
    }

    let starts: HashSet<_> = from_map
        .keys()
        .filter(|k| !to_map.contains_key(*k))
        .cloned()
        .collect();

    let mut result = vec![];
    let mut visited = HashSet::new();

    for start in starts {
        let mut path = vec![start.clone()];
        let mut current = start.clone();
        let _ = visited.insert(current.clone());

        while let Some(next) = from_map.get(&current) {
            if visited.contains(next) {
                break;
            }
            path.push(next.clone());
            let _ = visited.insert(next.clone());
            current = next.clone();
        }

        result.push(path);
    }

    for (from, to) in pairs {
        if !visited.contains(&from) && !visited.contains(&to) {
            result.push(vec![from.clone(), to.clone()]);
            let _ = visited.insert(from);
            let _ = visited.insert(to);
        }
    }

    result
}

impl Optimize<FunctionDefinition> for SimplifyCfgMerge {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let (cfg, bid_to_idx) = build_cfg(code);

        let merge_pairs: Vec<(BlockId, BlockId)> = code
            .blocks
            .iter()
            .filter_map(|(bid, block)| {
                let idx = bid_to_idx.get(bid).unwrap();
                let in_nodes = cfg.edges_directed(*idx, Incoming).collect::<Vec<_>>();
                if in_nodes.len() == 1 {
                    let prev_bid = cfg[in_nodes[0].source()];
                    let prev_blk = code.blocks.get(&prev_bid).unwrap();
                    prev_blk.exit.as_jump().map(|_| (prev_bid, bid.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let lists = merge_block_paths(merge_pairs);
        // dbg!(&lists);

        // for block list of a -> b -> c -> d
        // we need to relocate the instruction offset in b, c, d
        // and set the exit of a to be d's
        // and remove b, c, d
        for list in lists {
            assert!(list.len() > 1);
            let mut start_bid = list[0];
            let mut start_blk = code.blocks.remove(&start_bid).unwrap();
            let mut start_iid = start_blk.instructions.len();

            let mut prev_args = start_blk.exit.as_jump().cloned();

            for (idx, next) in list.iter().enumerate().skip(1) {
                let mut next_blk = code.blocks.remove(next).unwrap();
                next_blk.relocate(
                    start_bid,
                    start_blk.instructions.len(),
                    prev_args.as_ref().map(|p| &p.args[..]),
                );
                start_blk.instructions.extend(next_blk.instructions);

                prev_args = next_blk.exit.as_jump().cloned();

                if idx == list.len() - 1 {
                    start_blk.exit = next_blk.exit;
                }
            }
            let _ = code.blocks.insert(start_bid, start_blk);
        }

        changed
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgEmpty {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let (cfg, bid_to_idx) = build_cfg(code);
        let empty_blocks = code
            .blocks
            .iter()
            .filter_map(|(bid, block)| {
                if *bid == code.bid_init {
                    None
                } else if block.instructions.is_empty() && block.phinodes.is_empty() {
                    Some(*bid)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        let mut should_remove = false;

        for empty_bid in empty_blocks {
            let mut empty_blk = code.blocks.get(&empty_bid).unwrap();
            let next_exit = empty_blk.exit.clone();

            let idx = bid_to_idx.get(&empty_bid).unwrap();
            let edges = cfg.edges_directed(*idx, Incoming);
            for edge in edges {
                let f = cfg[edge.source()];

                match code.blocks.get_mut(&f).map(|x| &mut x.exit).unwrap() {
                    BlockExit::Jump { .. } => {
                        // us: jmp
                        // next: jmp or return
                        if matches!(next_exit, BlockExit::Jump { .. } | BlockExit::Return { .. }) {
                            code.blocks.get_mut(&f).unwrap().exit = next_exit.clone();
                        }
                    }
                    BlockExit::ConditionalJump {
                        condition,
                        arg_then,
                        arg_else,
                    } => {
                        // us: condition
                        // next: jmp
                        if let BlockExit::Jump { arg } = &next_exit {
                            if arg_then.bid == empty_bid {
                                *arg_then = arg.clone();
                            }
                            if arg_else.bid == empty_bid {
                                *arg_else = arg.clone();
                            }
                        }
                    }
                    BlockExit::Switch {
                        value,
                        default,
                        cases,
                    } => {
                        // us: switch
                        // next: jmp
                        if let BlockExit::Jump { arg } = &next_exit {
                            if default.bid == empty_bid {
                                *default = arg.clone();
                            }
                            cases.iter_mut().for_each(|(_, j)| {
                                if j.bid == empty_bid {
                                    *j = arg.clone();
                                }
                            });
                        }
                    }
                    _ => {}
                }
            }
        }

        changed
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{
        FunctionPass, SimplifyCfg, SimplifyCfgConstProp, SimplifyCfgEmpty, SimplifyCfgMerge,
        SimplifyCfgReach, test_opt,
    };

    #[test]
    fn t1() {
        // test_opt(
        //     &Path::new("examples/simplify_cfg/const_prop.input.ir"),
        //     &Path::new("examples/simplify_cfg/const_prop.output.ir"),
        //     &mut FunctionPass::<SimplifyCfgConstProp>::default(),
        // );

        // test_opt(
        //     &Path::new("examples/simplify_cfg/reach.input.ir"),
        //     &Path::new("examples/simplify_cfg/reach.output.ir"),
        //     &mut FunctionPass::<SimplifyCfgReach>::default(),
        // );

        test_opt(
            &Path::new("examples/simplify_cfg/empty.input.ir"),
            &Path::new("examples/simplify_cfg/empty.output.ir"),
            &mut FunctionPass::<SimplifyCfgEmpty>::default(),
        );

        // test_opt(
        //     &Path::new("examples/simplify_cfg/merge.input.ir"),
        //     &Path::new("examples/simplify_cfg/merge.output.ir"),
        //     &mut FunctionPass::<SimplifyCfgMerge>::default(),
        // );
    }

    #[test]
    fn test_basic() {
        test_opt(
            &Path::new("examples/ir0/switch-in-loop.ir"),
            &Path::new("examples/ir1/switch-in-loop.ir"),
            &mut SimplifyCfg::default(),
        );
    }
}
