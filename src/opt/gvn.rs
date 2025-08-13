use core::ops::Deref;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use itertools::{Either, izip};
use lang_c::ast;
use petgraph::Graph;
use petgraph::algo::dominators::simple_fast;
use petgraph::graph::NodeIndex;

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum InstKind {
    Nop,
    Bin(ast::BinaryOperator),
    Unary(ast::UnaryOperator),
    Value,
    Store,
    Load,
    Call,
    TypeCast,
    GetElementPtr,
}

impl From<&Instruction> for InstKind {
    fn from(value: &Instruction) -> Self {
        match value {
            Instruction::Nop => Self::Nop,
            Instruction::Value { value } => Self::Value,
            Instruction::BinOp {
                op,
                lhs,
                rhs,
                dtype,
            } => Self::Bin(op.clone()),
            Instruction::UnaryOp { op, operand, dtype } => Self::Unary(op.clone()),
            Instruction::Store { ptr, value } => Self::Store,
            Instruction::Load { ptr } => Self::Load,
            Instruction::Call {
                callee,
                args,
                return_type,
            } => Self::Call,
            Instruction::TypeCast {
                value,
                target_dtype,
            } => Self::TypeCast,
            Instruction::GetElementPtr { ptr, offset, dtype } => Self::GetElementPtr,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Expr {
    /// for convenience, opcode might be better
    kind: InstKind,
    /// numbers of the operands if it's not a const
    /// we use btree-set to make sure that they're ordered
    numbers: BTreeSet<usize>,
    consts: BTreeSet<Constant>,
    dtype: Dtype,
}

impl Expr {
    fn new(insn: &Instruction, tbl: &ValueTable) -> Expr {
        let mut numbers = BTreeSet::new();
        let mut consts = BTreeSet::new();
        insn.visit_ops(|op| match op {
            Operand::Constant(c) => {
                let _ = consts.insert(c.clone());
            }
            Operand::Register { rid, dtype } => {
                let num = match tbl.reg.get(rid) {
                    Some(v) => v,
                    None => {
                        dbg!(tbl);
                        dbg!(insn);
                        panic!("{}", rid);
                    }
                };
                let _ = numbers.insert(*num);
            }
        });
        let dtype = insn.dtype();
        Self {
            kind: insn.into(),
            numbers,
            consts,
            dtype,
        }
    }
}

#[derive(Clone, Debug)]
struct ValueTable {
    next_value_num: usize,
    /// numbering of registers
    reg: HashMap<RegisterId, usize>,
    /// numbering of expressions
    expr: HashMap<Expr, usize>,
    /// from block unique instruction index to actual Operand(s)
    /// COVEAT: RegisterId cannot be allocs
    leader: HashMap<(BlockId, usize), RegisterId>,
}

impl Default for ValueTable {
    fn default() -> Self {
        Self {
            next_value_num: 1,
            reg: Default::default(),
            expr: Default::default(),
            leader: Default::default(),
        }
    }
}

impl ValueTable {
    fn alloc_num(&mut self) -> usize {
        let val = self.next_value_num;
        self.next_value_num += 1;
        val
    }
}

pub type Gvn = FunctionPass<GvnInner>;

#[derive(Default, Clone, Copy, Debug)]
pub struct GvnInner {}

impl Optimize<FunctionDefinition> for GvnInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut changed = false;
        let (cfg, bid_to_idx) = build_cfg(code);
        let dom = simple_fast(&cfg, *bid_to_idx.get(&code.bid_init).unwrap());
        dbg!(&dom);

        let mut tbls = HashMap::new();

        let mut queue = VecDeque::from(code.reverse_post_order());
        let mut visited = HashSet::new();

        while !queue.is_empty() {
            let bid = queue.pop_front().unwrap();
            if !visited.insert(bid) {
                continue;
            }
            let mut block = code.blocks.remove(&bid).unwrap();

            // TODO: use idom's value tbl
            let mut tbl = if bid == code.bid_init {
                ValueTable::default()
            } else {
                let idom_node_idx = dom
                    .immediate_dominator(*bid_to_idx.get(&bid).unwrap())
                    .unwrap();
                let idom = cfg[idom_node_idx];
                tbls.get(&idom).cloned().unwrap()
            };

            // handle phinodes
            for aid in 0..block.phinodes.len() {
                let mut numbers = vec![];
                for pred in predecessors(&cfg, &bid_to_idx, &bid) {
                    let pred_block = code.blocks.get_mut(&pred).unwrap();
                    let pred_tbl = tbls.get(&pred).unwrap();
                    pred_block.exit.walk_jump_args(|arg| {
                        if let Some((reg_id, _)) = arg.args[aid].get_register() {
                            numbers.push(pred_tbl.reg.get(reg_id).cloned().unwrap());
                        }
                    });
                }

                // For a phinode %p = φ(%a, %b) of B,
                if bid != code.bid_init && numbers.iter().all(|&n| n == numbers[0]) {
                    // If RT(%a)=RT(%b)=Ⓝ, then RT(%p)=Ⓝ.
                    let reg = RegisterId::Arg { bid, aid };
                    let _ = tbl.reg.insert(reg, numbers[0]);
                    let _ = tbl.leader.insert((bid, numbers[0]), reg);
                } else {
                    // Otherwise, %p is assigned with a new number
                    let num = tbl.alloc_num();
                    let reg = RegisterId::Arg { bid, aid };
                    let _ = tbl.reg.insert(reg, num);
                    let _ = tbl.leader.insert((bid, num), reg);
                }
            }

            let mut replaces = HashMap::new();

            // handle instructions
            for (iid, insn) in block.instructions.iter_mut().enumerate() {
                let insn = insn.inner_mut();
                insn.visit_ops_mut(|op| {
                    if let Operand::Register { rid, dtype } = op
                        && let RegisterId::Temp { iid, .. } = rid
                        && let Some(&replace) = replaces.get(iid)
                    {
                        let new_rid = tbl.leader.get(&(bid, replace)).cloned().unwrap();
                        *rid = new_rid;
                    }
                });

                let expr = Expr::new(insn, &tbl);
                match tbl.expr.get(&expr) {
                    // If LT@pc(Ⓝ) exists, then replaces %i with LT@pc(Ⓝ).
                    Some(num) => {
                        changed = true;
                        let _ = replaces.insert(iid, *num);
                    }
                    None => {
                        let num = tbl.alloc_num();
                        let _ = tbl.expr.insert(expr, num);

                        let mut n_exists_for_all_preds = true;
                        let preds = predecessors(&cfg, &bid_to_idx, &bid);
                        for &pred in &preds {
                            let pred_block = code.blocks.get_mut(&pred).unwrap();
                            let pred_tbl = tbls.get(&pred).unwrap();
                            if !pred_tbl.leader.contains_key(&(pred, num)) {
                                n_exists_for_all_preds = false;
                                break;
                            }
                        }

                        // If [LT@B final(Ⓝ) exists for all predecessor B of %i’s block],
                        // then creates a new phinode, say %p=φ({LT@B final(Ⓝ) | B ∈ pred(%i)});
                        // let LT@pc(Ⓝ) = %p; and replaces %i with %p.
                        if !preds.is_empty() && n_exists_for_all_preds {
                            changed = true;
                            todo!()
                        } else {
                            // Otherwise, let LT@pc(Ⓝ) = %i.
                            let reg = RegisterId::Temp { bid, iid };
                            let _ = tbl.reg.insert(reg, num);
                            let _ = tbl.leader.insert((bid, num), reg);
                        }
                    }
                }
            }

            // dbg!(bid, &tbl);
            let _ = code.blocks.insert(bid, block);

            let _ = tbls.insert(bid, tbl);

            for next in successors(&cfg, &bid_to_idx, &bid) {
                queue.push_back(next);
            }
        }

        changed
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{FunctionPass, Gvn, test_opt};

    #[test]
    fn test_gvn_basic() {
        // 0->1, 0->2, 1->3, 2->3
        test_opt(
            &Path::new("examples/gvn/gvn.input.ir"),
            &Path::new("examples/gvn/gvn.output.ir"),
            &mut Gvn::default(),
        );
    }

    #[test]
    fn test_gvn_basic2() {
        test_opt(
            &Path::new("examples/ir3/foo.ir"),
            &Path::new("examples/ir4/foo.ir"),
            &mut Gvn::default(),
        );
    }
}
