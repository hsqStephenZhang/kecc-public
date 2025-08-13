use core::ops::{Deref, DerefMut};
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::*;

pub type Mem2reg = FunctionPass<Mem2regInner>;

#[derive(Default, Clone, Copy, Debug)]
pub struct Mem2regInner {}

impl Optimize<FunctionDefinition> for Mem2regInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let (cfg, bid_to_idx) = build_cfg(code);
        let df = dominance_frontiers(&cfg, bid_to_idx.get(&code.bid_init).cloned().unwrap());
        dbg!(cfg);
        dbg!(df);

        changed
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{FunctionPass, Mem2reg, test_opt};

    #[test]
    fn t1() {
        test_opt(
            &Path::new("examples/mem2reg/mem2reg.input.ir"),
            &Path::new("examples/mem2reg/mem2reg.output.ir"),
            &mut Mem2reg::default(),
        );
    }

    #[test]
    fn test_basic() {
        test_opt(
            &Path::new("examples/ir1/foo.ir"),
            &Path::new("examples/ir2/foo.ir"),
            &mut Mem2reg::default(),
        );
    }
}
