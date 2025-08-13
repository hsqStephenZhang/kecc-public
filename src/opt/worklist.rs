use std::{
    collections::{HashSet, VecDeque},
    hash::Hash,
};

use crate::ir::BlockId;

pub(crate) trait Idx: Hash + Eq + Copy {}

impl Idx for BlockId {}
impl Idx for petgraph::graph::NodeIndex {}

#[derive(Default)]
pub(crate) struct WorkList<T> {
    queue: VecDeque<T>,
    set: HashSet<T>,
}

impl<T: Idx> WorkList<T> {
    pub(crate) fn new() -> Self {
        Self {
            queue: VecDeque::new(),
            set: HashSet::new(),
        }
    }

    pub(crate) fn insert(&mut self, item: T) -> bool {
        if self.set.insert(item) {
            self.queue.push_back(item);
            true
        } else {
            false
        }
    }

    pub(crate) fn pop(&mut self) -> Option<T> {
        self.queue.pop_front()
    }
}

#[cfg(test)]
mod tests {
    use petgraph::{Graph, graph::NodeIndex};

    use crate::{ir::BlockId, opt::worklist::WorkList};

    #[test]
    fn test1() {
        let mut cfg: Graph<BlockId, ()> = Graph::new();
        let a = cfg.add_node(BlockId(1));
        let b = cfg.add_node(BlockId(2));
        let c = cfg.add_node(BlockId(3));

        let mut worklist: WorkList<NodeIndex> = WorkList::new();
        for n in cfg.node_indices() {
            let _ = worklist.insert(n);
        }

        while let Some(cur) = worklist.pop() {
            println!("{:?}", cur);
        }
    }
}
