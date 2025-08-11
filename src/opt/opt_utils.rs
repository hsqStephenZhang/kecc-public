//! Utilities for implementing optimizations.
//!
//! You can freely add utilities commonly used in the implementation of multiple optimizations here.

use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use itertools::izip;
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
