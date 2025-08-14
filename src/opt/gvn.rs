use core::ops::Deref;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

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

impl TryFrom<&Instruction> for InstKind {
    type Error = ();

    fn try_from(value: &Instruction) -> Result<Self, Self::Error> {
        let res = match value {
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
        };
        Ok(res)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Expr {
    /// for convenience, opcode might be better
    kind: InstKind,
    /// numbers of the operands if it's not a const
    /// we use btree-set to make sure that they're ordered
    ops: Vec<Either<usize, Constant>>,
    // usage of alloc and its version
    locals: BTreeMap<usize, usize>,
    dtype: Dtype,
}

fn is_commutative(op: &ast::BinaryOperator) -> bool {
    use ast::BinaryOperator::*;
    matches!(
        op,
        Plus | Multiply | BitwiseAnd | BitwiseOr | BitwiseXor | Equals | NotEquals
    )
}

impl Expr {
    fn new(insn: &Instruction, tbl: &ValueTable, memver: &HashMap<usize, usize>) -> Option<Expr> {
        let mut ops = Vec::new();
        let mut locals = BTreeMap::new();
        let dtype = insn.dtype();
        let kind = insn.try_into().ok()?;

        insn.visit_ops(|op| match op {
            Operand::Constant(c) => {
                let _ = ops.push(Either::Right(c.clone()));
            }
            Operand::Register { rid, dtype } => {
                if let RegisterId::Local { aid } = rid {
                    let ver = memver.get(aid).cloned().unwrap_or_default();
                    let _ = locals.insert(*aid, ver);
                } else if let Some(num) = tbl.reg.get(rid) {
                    let _ = ops.push(Either::Left(*num));
                } else {
                    // TODO: how to handle this?
                    return;
                }
            }
        });
        if let InstKind::Bin(op) = &kind {
            if is_commutative(op) {
                ops.sort_unstable();
            }
        }

        Some(Self {
            kind,
            ops,
            locals,
            dtype,
        })
    }
}
#[derive(Clone, Debug)]
struct ValueTable {
    next_value_num: usize,
    /// numbering of registers
    reg: HashMap<RegisterId, usize>,
    /// from block unique instruction index to actual Operand(s)
    /// COVEAT: RegisterId cannot be allocs
    leader: HashMap<usize, RegisterId>,
}

impl Default for ValueTable {
    fn default() -> Self {
        Self {
            next_value_num: 1,
            reg: Default::default(),
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

        let mut next_expr_num = 1;
        let mut alloc_num = || {
            let val = next_expr_num;
            next_expr_num += 1;
            val
        };
        let mut expr_tbl = HashMap::new();

        let (cfg, bid_to_idx) = build_cfg(code);
        let dom = simple_fast(&cfg, *bid_to_idx.get(&code.bid_init).unwrap());

        let mut value_tbls = HashMap::new();
        let mut replaces: HashMap<BlockId, HashMap<usize, usize>> = HashMap::new();

        for bid in code.reverse_post_order() {
            let mut block = code.blocks.remove(&bid).unwrap();

            let mut value_tbl = if bid == code.bid_init {
                ValueTable::default()
            } else {
                let idom_node_idx = dom
                    .immediate_dominator(*bid_to_idx.get(&bid).unwrap())
                    .unwrap();
                let idom = cfg[idom_node_idx];
                value_tbls.get(&idom).cloned().unwrap()
            };

            let preds = predecessors(&cfg, &bid_to_idx, &bid);

            // handle phinodes
            for aid in 0..block.phinodes.len() {
                let mut numbers = vec![];
                for pred in &preds {
                    let pred_tbl = match value_tbls.get(pred) {
                        Some(t) => t,
                        None => {
                            continue;
                        }
                    };
                    let pred_block = code.blocks.get_mut(&pred).unwrap();
                    pred_block.exit.walk_jump_args(|arg| {
                        if arg.bid == bid {
                            // dbg!((pred, aid, &arg.args));
                            if let Some((reg_id, _)) = arg.args[aid].get_register() {
                                numbers.push(pred_tbl.reg.get(reg_id).cloned().unwrap_or_else(
                                    || {
                                        // dbg!((reg_id, pred_tbl, &expr_tbl));
                                        todo!()
                                    },
                                ));
                            }
                        }
                    });
                }
                // dbg!((bid, &numbers));

                // For a phinode %p = φ(%a, %b) of B, If RT(%a)=RT(%b)=Ⓝ, then RT(%p)=Ⓝ.
                if bid != code.bid_init
                    && !numbers.is_empty()
                    && numbers.iter().all(|&n| n == numbers[0])
                {
                    let reg = RegisterId::Arg { bid, aid };
                    let _ = value_tbl.reg.insert(reg, numbers[0]);
                } else {
                    // Otherwise, %p is assigned with a new number
                    let num = alloc_num();
                    let reg = RegisterId::Arg { bid, aid };
                    let _ = value_tbl.reg.insert(reg, num);
                    let _ = value_tbl.leader.insert(num, reg);
                }
            }

            // version number for each alloc in this block
            let mut memver = HashMap::new();
            // handle instructions
            for (iid, insn) in block.instructions.iter_mut().enumerate() {
                // println!("{}", insn);
                let insn = insn.inner_mut();
                insn.visit_ops_mut(|op| {
                    if let Operand::Register { rid, dtype } = op
                        && let RegisterId::Temp { iid, bid } = rid
                        && let Some(replace) = replaces.get(bid).and_then(|m| m.get(iid))
                    {
                        let new_rid = value_tbl.leader.get(replace).cloned().unwrap_or_else(|| {
                            dbg!((&value_tbl, replace, &expr_tbl));
                            panic!();
                        });
                        *rid = new_rid;
                    }
                });

                // update memory version
                if let Instruction::Store { ptr, .. } | Instruction::Load { ptr } = insn
                    && let Some((rid, _)) = ptr.get_register()
                    && let RegisterId::Local { aid } = rid
                {
                    *memver.entry(*aid).or_default() += 1;
                }

                // lookup or insert expr
                let expr = match Expr::new(insn, &value_tbl, &memver) {
                    Some(e) => e,
                    None => continue,
                };
                let num = match expr_tbl.get(&expr) {
                    Some(num) => *num,
                    None => {
                        let num = alloc_num();
                        let _ = expr_tbl.insert(expr, num);
                        num
                    }
                };
                let _ = value_tbl.reg.insert(RegisterId::Temp { bid, iid }, num);

                // If LT@pc(Ⓝ) exists, then replaces %i with LT@pc(Ⓝ).
                if value_tbl.leader.contains_key(&num) {
                    let _ = replaces.entry(bid).or_default().insert(iid, num);
                    continue;
                }

                // if we should insert phinode
                let mut pred_has_num_cnt = 0;
                for &pred in &preds {
                    if value_tbls
                        .get(&pred)
                        .and_then(|m| m.leader.get(&num))
                        .is_some()
                    {
                        pred_has_num_cnt += 1;
                    }
                }

                // If [LT@B final(Ⓝ) exists for all predecessor B of %i’s block],
                // then creates a new phinode, say %p=φ({LT@B final(Ⓝ) | B ∈ pred(%i)});
                // and:
                //  1. LT@pc(Ⓝ) = %p;
                //  2. replaces %i with %p.
                if pred_has_num_cnt == preds.len()
                    && pred_has_num_cnt >= 2
                    && !insn.dtype().is_unit()
                {
                    // dbg!(&insn);
                    // dbg!(&preds);
                    changed = true;
                    let _ = value_tbl.leader.insert(
                        num,
                        RegisterId::Arg {
                            bid,
                            aid: block.phinodes.len(),
                        },
                    );
                    block.phinodes.push(Named::new(None, insn.dtype()));
                    // println!("should replace with phi at {}-{}, {}", bid, iid, insn);
                    let _ = replaces.entry(bid).or_default().insert(iid, num);

                    // fix predecessors
                    for &pred in &preds {
                        let pred_tbl = match value_tbls.get(&pred) {
                            Some(t) => t,
                            None => continue,
                        };
                        let rid = pred_tbl.leader.get(&num).cloned().unwrap();
                        let pred_block = code.blocks.get_mut(&pred).unwrap();
                        pred_block.exit.walk_jump_args_mut(|arg| {
                            arg.args.push(Operand::Register {
                                rid,
                                dtype: insn.dtype(),
                            });
                        });
                    }
                } else {
                    // Otherwise, let LT@pc(Ⓝ) = %i.
                    let _ = value_tbl.leader.insert(num, RegisterId::Temp { bid, iid });
                }
            }

            let mut update_op = |op: &mut Operand| {
                if let Some((rid, _)) = op.get_register_mut()
                    && let RegisterId::Temp { bid, iid } = rid
                    && let Some(replace) = replaces.get(bid).and_then(|m| m.get(iid))
                {
                    let replace = value_tbl.leader.get(replace).cloned().unwrap();
                    *rid = replace;
                }
            };

            block.exit.visit_op(update_op);

            block.exit.walk_jump_args_mut(|arg| {
                for op in &mut arg.args {
                    update_op(op);
                }
            });

            // dbg!((bid, &value_tbl));

            let _ = code.blocks.insert(bid, block);

            let _ = value_tbls.insert(bid, value_tbl);
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

        test_opt(
            &Path::new("examples/gvn/temp.input.ir"),
            &Path::new("examples/gvn/temp.output.ir"),
            &mut Gvn::default(),
        );
    }

    #[test]
    fn test_gvn_basic2() {
        test_opt(
            &Path::new("examples/ir3/pointer.ir"),
            &Path::new("examples/ir4/pointer.ir"),
            &mut Gvn::default(),
        );

        test_opt(
            &Path::new("examples/ir3/temp2.ir"),
            &Path::new("examples/ir4/temp2.ir"),
            &mut Gvn::default(),
        );

        test_opt(
            &Path::new("examples/ir3/logical_op.ir"),
            &Path::new("examples/ir4/logical_op.ir"),
            &mut Gvn::default(),
        );
    }
}
