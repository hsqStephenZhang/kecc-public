use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use itertools::izip;
use petgraph::prelude::*;

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::*;

pub type SimplifyCfg = FunctionPass<
    Repeat<(
        SimplifyCfgConstProp,
        (SimplifyCfgReach, (SimplifyCfgMerge, SimplifyCfgEmpty)),
    )>,
>;

fn build_cfg(def: &FunctionDefinition) -> (Graph<BlockId, ()>, HashMap<BlockId, NodeIndex>) {
    let mut graph = Graph::new();
    let mut bid_to_idx = HashMap::new();
    for (&bid, _) in &def.blocks {
        let idx = graph.add_node(bid);
        let _ = bid_to_idx.insert(bid, idx);
    }

    for (bid, block) in &def.blocks {
        let idx_from = bid_to_idx.get(bid).unwrap();
        let exit = &block.exit;
        match exit {
            BlockExit::Jump { arg } => {
                let idx_to = bid_to_idx.get(&arg.bid).unwrap();
                let _ = graph.add_edge(*idx_from, *idx_to, ());
            }
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                let idx_to1 = bid_to_idx.get(&arg_then.bid).unwrap();
                let idx_to2 = bid_to_idx.get(&arg_else.bid).unwrap();
                let _ = graph.add_edge(*idx_from, *idx_to1, ());
                let _ = graph.add_edge(*idx_from, *idx_to2, ());
            }
            BlockExit::Switch {
                value,
                default,
                cases,
            } => {
                let idx_to_default = bid_to_idx.get(&default.bid).unwrap();
                let _ = graph.add_edge(*idx_from, *idx_to_default, ());

                for (_, arg) in cases {
                    let idx_to = bid_to_idx.get(&arg.bid).unwrap();
                    let _ = graph.add_edge(*idx_from, *idx_to, ());
                }
            }
            _ => {}
        }
    }

    (graph, bid_to_idx)
}

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
        let mut queue = vec![code.bid_init];
        while !queue.is_empty() {
            let cur = queue.pop().unwrap();
            let _ = reachable.insert(cur);
            let block = code.blocks.get(&cur).unwrap();
            match &block.exit {
                BlockExit::Jump { arg } => {
                    if !reachable.contains(&arg.bid) {
                        queue.push(arg.bid);
                    }
                }
                BlockExit::ConditionalJump {
                    arg_then, arg_else, ..
                } => {
                    if !reachable.contains(&arg_then.bid) {
                        queue.push(arg_then.bid);
                    }
                    if !reachable.contains(&arg_else.bid) {
                        queue.push(arg_else.bid);
                    }
                }
                BlockExit::Switch {
                    value,
                    default,
                    cases,
                } => {
                    if !reachable.contains(&default.bid) {
                        queue.push(default.bid);
                    }
                    for case in cases {
                        if !reachable.contains(&case.1.bid) {
                            queue.push(case.1.bid);
                        }
                    }
                }
                _ => {}
            }
        }

        if reachable.len() != code.blocks.len() {
            changed = true;
            let all = code.blocks.keys().cloned().collect::<Vec<_>>();
            for bid in all {
                if !reachable.contains(&bid) {
                    let _ = code.blocks.remove(&bid);
                }
            }
        }

        changed
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgMerge {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let (cfg, bid_to_idx) = build_cfg(code);

        let merge_pairs = code
            .blocks
            .iter()
            .filter_map(|(bid, block)| {
                let idx = bid_to_idx.get(bid).unwrap();
                let in_nodes = cfg.edges_directed(*idx, Incoming).collect::<Vec<_>>();
                if in_nodes.len() == 1 {
                    let prev_node = cfg[in_nodes[0].source()];
                    Some((prev_node, bid.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        for (prev, next) in merge_pairs {
            let mut next_blk = code.blocks.remove(&next).unwrap();
            let prev_blk = code.blocks.get_mut(&prev).unwrap();
            if !next_blk.phinodes.is_empty()
                && let BlockExit::Jump { arg } = &prev_blk.exit
            {
                assert_eq!(next_blk.phinodes.len(), arg.args.len());
                let args = next_blk
                    .phinodes
                    .iter()
                    .cloned()
                    .zip(arg.args.iter().cloned())
                    .collect::<HashMap<_, _>>();

                for insn in &mut next_blk.instructions {
                    let insn = insn.inner_mut();
                    insn.apply_args(&arg.args);
                }
                prev_blk.instructions.extend(next_blk.instructions);
            }
            next_blk.exit.set_op_bid(prev);
            prev_blk.exit = next_blk.exit;
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
                if block.instructions.is_empty() && block.phinodes.is_empty() {
                    Some(*bid)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        for empty_bid in empty_blocks {
            let next_exit = code.blocks.get(&empty_bid).map(|x| x.exit.clone()).unwrap();

            let idx = bid_to_idx.get(&empty_bid).unwrap();
            for edge in cfg.edges_directed(*idx, Incoming) {
                let f = cfg[edge.source()];

                match code.blocks.get(&f).map(|x| x.exit.clone()).unwrap() {
                    BlockExit::Jump { arg } => {
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
                            code.blocks.get_mut(&f).unwrap().exit = BlockExit::ConditionalJump {
                                condition,
                                arg_then: arg.clone(),
                                arg_else: arg.clone(),
                            };
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
        FunctionPass, SimplifyCfgConstProp, SimplifyCfgEmpty, SimplifyCfgMerge, SimplifyCfgReach,
        test_opt,
    };

    #[test]
    fn t1() {
        test_opt(
            &Path::new("examples/simplify_cfg/const_prop.input.ir"),
            &Path::new("examples/simplify_cfg/const_prop.output.ir"),
            &mut FunctionPass::<SimplifyCfgConstProp>::default(),
        );

        test_opt(
            &Path::new("examples/simplify_cfg/reach.input.ir"),
            &Path::new("examples/simplify_cfg/reach.output.ir"),
            &mut FunctionPass::<SimplifyCfgReach>::default(),
        );

        test_opt(
            &Path::new("examples/simplify_cfg/merge.input.ir"),
            &Path::new("examples/simplify_cfg/merge.output.ir"),
            &mut FunctionPass::<SimplifyCfgMerge>::default(),
        );

        test_opt(
            &Path::new("examples/simplify_cfg/empty.input.ir"),
            &Path::new("examples/simplify_cfg/empty.output.ir"),
            &mut FunctionPass::<SimplifyCfgEmpty>::default(),
        );
    }
}
