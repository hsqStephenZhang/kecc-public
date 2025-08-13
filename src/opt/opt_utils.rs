//! Utilities for implementing optimizations.
//!
//! You can freely add utilities commonly used in the implementation of multiple optimizations here.

use std::collections::{HashMap, HashSet};
use std::hash::DefaultHasher;
use std::ops::Deref;

use itertools::izip;
use petgraph::algo::dominators::{Dominators, simple_fast};
use petgraph::prelude::*;
use serde::de;

use crate::ir::{BlockExit, BlockId, FunctionDefinition};

pub(crate) fn build_cfg(
    def: &FunctionDefinition,
) -> (Graph<BlockId, ()>, HashMap<BlockId, NodeIndex>) {
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
                let idx_to1 = match bid_to_idx.get(&arg_then.bid) {
                    Some(v) => v,
                    None => {
                        dbg!(bid_to_idx);
                        dbg!(exit);
                        dbg!(def.blocks.keys());
                        panic!();
                    },
                };
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

pub(crate) fn predecessors(
    cfg: &Graph<BlockId, ()>,
    bid_to_idx: &HashMap<BlockId, NodeIndex>,
    bid: &BlockId,
) -> Vec<BlockId> {
    let idx = bid_to_idx.get(bid).unwrap();
    cfg.edges_directed(*idx, Incoming)
        .into_iter()
        .map(|edge| cfg[edge.source()])
        .collect::<Vec<_>>()
}

#[allow(unused)]
pub(crate) fn successors(
    cfg: &Graph<BlockId, ()>,
    bid_to_idx: &HashMap<BlockId, NodeIndex>,
    bid: &BlockId,
) -> Vec<BlockId> {
    let idx = bid_to_idx.get(bid).unwrap();
    cfg.edges_directed(*idx, Outgoing)
        .into_iter()
        .map(|edge| cfg[edge.target()])
        .collect::<Vec<_>>()
}

pub(crate) fn dominance_frontiers(
    cfg: &Graph<BlockId, ()>,
    entry_idx: NodeIndex,
) -> HashMap<BlockId, HashSet<BlockId>> {
    let dom: Dominators<NodeIndex> = simple_fast(cfg, entry_idx);

    let mut df: HashMap<NodeIndex, HashSet<NodeIndex>> = HashMap::new();

    for edge in cfg.edge_references() {
        let a = edge.source();
        let b = edge.target();
        let mut x = a;
        while let Some(mut iter) = dom.strict_dominators(b)
            && !iter.any(|node| node == x)
        {
            let mut entry = df.entry(x).or_default();
            let _ = entry.insert(b);

            x = match dom.immediate_dominator(x) {
                Some(x) => x,
                None => break,
            }
        }
    }

    df.into_iter()
        .map(|(k, v)| {
            (
                cfg[k],
                v.into_iter().map(|v| cfg[v]).collect::<HashSet<_>>(),
            )
        })
        .collect::<HashMap<_, _>>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_df() {
        let mut cfg: Graph<BlockId, ()> = Graph::new();
        let a = cfg.add_node(BlockId(1));
        let b = cfg.add_node(BlockId(2));
        let c = cfg.add_node(BlockId(3));
        let d = cfg.add_node(BlockId(4));
        let e = cfg.add_node(BlockId(5));
        let f = cfg.add_node(BlockId(6));

        // c is the root
        let _ = cfg.add_edge(c, a, ());
        let _ = cfg.add_edge(c, b, ());
        let _ = cfg.add_edge(a, f, ());
        let _ = cfg.add_edge(f, d, ());
        let _ = cfg.add_edge(b, d, ());
        let _ = cfg.add_edge(b, e, ());
        let _ = cfg.add_edge(d, c, ());

        let dom = simple_fast(&cfg, c);
        let df = dominance_frontiers(&cfg, c);
        assert_eq!(*df.get(&BlockId(3)).unwrap(), HashSet::from([BlockId(3)]));
        assert_eq!(*df.get(&BlockId(4)).unwrap(), HashSet::from([BlockId(3)]));
    }
}
