//! # Homework: IR Generation
//!
//! The goal of this homework is to translate the components of a C file into KECC IR. While doing
//! so, you will familarize yourself with the structure of KECC IR, and understand the semantics of
//! C in terms of KECC.
//!
//! We highly recommend checking out the [slides][slides] and [github repo][github-qna-irgen] for
//! useful information.
//!
//! ## Guide
//!
//! ### High Level Guide
//!
//! Please watch the following video from 2020 along the lecture slides.
//! - [Intermediate Representation][ir]
//! - [IRgen (Overview)][irgen-overview]
//!
//! ### Coding Guide
//!
//! We highly recommend you copy-and-paste the code given in the following lecture videos from 2020:
//! - [IRgen (Code, Variable Declaration)][irgen-var-decl]
//! - [IRgen (Code, Function Definition)][irgen-func-def]
//! - [IRgen (Code, Statement 1)][irgen-stmt-1]
//! - [IRgen (Code, Statement 2)][irgen-stmt-2]
//!
//! The skeleton code roughly consists of the code for the first two videos, but you should still
//! watch them to have an idea of what the code is like.
//!
//! [slides]: https://docs.google.com/presentation/d/1SqtU-Cn60Sd1jkbO0OSsRYKPMIkul0eZoYG9KpMugFE/edit?usp=sharing
//! [ir]: https://youtu.be/7CY_lX5ZroI
//! [irgen-overview]: https://youtu.be/YPtnXlKDSYo
//! [irgen-var-decl]: https://youtu.be/HjARCUoK08s
//! [irgen-func-def]: https://youtu.be/Rszt9x0Xu_0
//! [irgen-stmt-1]: https://youtu.be/jFahkyxm994
//! [irgen-stmt-2]: https://youtu.be/UkaXaNw462U
//! [github-qna-irgen]: https://github.com/kaist-cp/cs420/labels/homework%20-%20irgen
use core::cmp::Ordering;
use core::convert::TryFrom;
use core::{fmt, mem};
use std::collections::{BTreeMap, HashMap};
use std::ops::Deref;

use itertools::{Either, izip};
use lang_c::ast::*;
use lang_c::driver::Parse;
use lang_c::span::Node;
use serde_json::json;
use thiserror::Error;

use crate::ir::{DtypeError, HasDtype, Instruction, JumpArg, Named};
use crate::write_base::WriteString;
use crate::*;

#[derive(Debug)]
pub struct IrgenError {
    pub code: String,
    pub message: IrgenErrorMessage,
}

impl IrgenError {
    pub fn new(code: String, message: IrgenErrorMessage) -> Self {
        Self { code, message }
    }

    pub fn other(code: String) -> Self {
        Self {
            code,
            message: IrgenErrorMessage::Other,
        }
    }
}

impl fmt::Display for IrgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\r\n\r\ncode: {}", self.message, self.code)
    }
}

/// Error format when a compiler error happens.
///
/// Feel free to add more kinds of errors.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum IrgenErrorMessage {
    /// For uncommon error
    #[error("{message}")]
    Misc { message: String },
    #[error("called object `{callee:?}` is not a function or function pointer")]
    NeedFunctionOrFunctionPointer { callee: ir::Operand },
    #[error("redefinition, `{name}`")]
    Redefinition { name: String },
    #[error("`{dtype}` conflicts prototype's dtype, `{protorype_dtype}`")]
    ConflictingDtype {
        dtype: ir::Dtype,
        protorype_dtype: ir::Dtype,
    },
    #[error("{dtype_error}")]
    InvalidDtype { dtype_error: DtypeError },
    #[error("l-value required as {message}")]
    RequireLvalue { message: String },
    #[error("other")]
    Other,
}

/// A C file going through IR generation.
#[derive(Default, Debug)]
pub struct Irgen {
    /// Declarations made in the C file (e.g, global variables and functions)
    decls: BTreeMap<String, ir::Declaration>,
    /// Type definitions made in the C file (e.g, typedef my_type = int;)
    typedefs: HashMap<String, ir::Dtype>,
    /// Structs defined in the C file,
    // TODO: explain how to use this.
    structs: HashMap<String, Option<ir::Dtype>>,
    /// Temporary counter for anonymous structs. One should not need to use this any more.
    struct_tempid_counter: usize,
}

impl Translate<Parse> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &Parse) -> Result<Self::Target, Self::Error> {
        self.translate(&source.unit)
    }
}

impl Translate<TranslationUnit> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &TranslationUnit) -> Result<Self::Target, Self::Error> {
        for ext_decl in &source.0 {
            match &ext_decl.node {
                ExternalDeclaration::Declaration(var) => {
                    self.add_declaration(&var.node)?;
                }
                ExternalDeclaration::StaticAssert(_) => {
                    panic!("ExternalDeclaration::StaticAssert is unsupported")
                }
                ExternalDeclaration::FunctionDefinition(func) => {
                    self.add_function_definition(&func.node)?;
                }
            }
        }

        let decls = mem::take(&mut self.decls);
        let structs = mem::take(&mut self.structs);
        Ok(Self::Target { decls, structs })
    }
}

impl Irgen {
    const BID_INIT: ir::BlockId = ir::BlockId(0);
    // `0` is used to create `BID_INIT`
    const BID_COUNTER_INIT: usize = 1;
    const TEMPID_COUNTER_INIT: usize = 0;

    /// Add a declaration. It can be either a struct, typedef, or a variable.
    fn add_declaration(&mut self, source: &Declaration) -> Result<(), IrgenError> {
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&source.specifiers).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
        let base_dtype = base_dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("{source:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        let base_dtype = if let ir::Dtype::Struct { name, fields, .. } = &base_dtype {
            if let Some(name) = name {
                let _ = self.structs.entry(name.to_string()).or_insert(None);
            }

            if fields.is_some() {
                base_dtype
                    .resolve_structs(&mut self.structs, &mut self.struct_tempid_counter)
                    .map_err(|e| {
                        IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::InvalidDtype { dtype_error: e },
                        )
                    })?
            } else {
                base_dtype
            }
        } else {
            base_dtype
        };

        for init_decl in &source.declarators {
            let declarator = &init_decl.node.declarator.node;
            let name = name_of_declarator(declarator);
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| {
                    IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::InvalidDtype { dtype_error: e },
                    )
                })?
                .deref()
                .clone();
            let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
            if !is_typedef && is_invalid_structure(&dtype, &self.structs) {
                return Err(IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::Misc {
                        message: "incomplete struct type".to_string(),
                    },
                ));
            }

            if is_typedef {
                // Add new typedef if nothing has been declared before
                let prev_dtype = self
                    .typedefs
                    .entry(name.clone())
                    .or_insert_with(|| dtype.clone());

                if prev_dtype != &dtype {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::ConflictingDtype {
                            dtype,
                            protorype_dtype: prev_dtype.clone(),
                        },
                    ));
                }

                continue;
            }

            // Creates a new declaration based on the dtype.
            let mut decl = ir::Declaration::try_from(dtype.clone()).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;

            // If `initializer` exists, convert initializer to a constant value
            if let Some(initializer) = init_decl.node.initializer.as_ref() {
                if !is_valid_initializer(&initializer.node, &dtype, &self.structs) {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::Misc {
                            message: "initializer is not valid".to_string(),
                        },
                    ));
                }

                match &mut decl {
                    ir::Declaration::Variable {
                        initializer: var_initializer,
                        ..
                    } => {
                        if var_initializer.is_some() {
                            return Err(IrgenError::new(
                                format!("{source:#?}"),
                                IrgenErrorMessage::Redefinition { name },
                            ));
                        }
                        *var_initializer = Some(initializer.node.clone());
                    }
                    ir::Declaration::Function { .. } => {
                        return Err(IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::Misc {
                                message: "illegal initializer (only variables can be initialized)"
                                    .to_string(),
                            },
                        ));
                    }
                }
            }

            self.add_decl(&name, decl)?;
        }

        Ok(())
    }

    /// Add a function definition.
    fn add_function_definition(&mut self, source: &FunctionDefinition) -> Result<(), IrgenError> {
        // Creates name and signature.
        let specifiers = &source.specifiers;
        let declarator = &source.declarator.node;

        let name = name_of_declarator(declarator);
        let name_of_params = name_of_params_from_function_declarator(declarator)
            .expect("declarator is not from function definition");

        let (base_dtype, is_typedef) = ir::Dtype::try_from_ast_declaration_specifiers(specifiers)
            .map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        if is_typedef {
            return Err(IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::Misc {
                    message: "function definition declared typedef".into(),
                },
            ));
        }

        let dtype = base_dtype
            .with_ast_declarator(declarator)
            .map_err(|e| {
                IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?
            .deref()
            .clone();
        let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        let signature = ir::FunctionSignature::new(dtype.clone());

        // Adds new declaration if nothing has been declared before
        let decl = ir::Declaration::try_from(dtype).unwrap();
        self.add_decl(&name, decl)?;

        // Prepare scope for global variable
        let global_scope: HashMap<_, _> = self
            .decls
            .iter()
            .map(|(name, decl)| {
                let dtype = decl.dtype();
                let pointer = ir::Constant::global_variable(name.clone(), dtype);
                let operand = ir::Operand::constant(pointer);
                (name.clone(), operand)
            })
            .collect();

        // Prepares for irgen pass.
        let mut irgen = IrgenFunc {
            return_type: signature.ret.clone(),
            bid_init: Irgen::BID_INIT,
            phinodes_init: Vec::new(),
            allocations: Vec::new(),
            blocks: BTreeMap::new(),
            bid_counter: Irgen::BID_COUNTER_INIT,
            tempid_counter: Irgen::TEMPID_COUNTER_INIT,
            typedefs: &self.typedefs,
            structs: &self.structs,
            // Initial symbol table has scope for global variable already
            symbol_table: vec![global_scope],
        };
        let mut context = Context::new(irgen.bid_init);

        // Enter variable scope for alloc registers matched with function parameters
        irgen.enter_scope();

        // Creates the init block that stores arguments.
        irgen
            .translate_parameter_decl(&signature, irgen.bid_init, &name_of_params, &mut context)
            .map_err(|e: IrgenErrorMessage| {
                IrgenError::new(format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"), e)
            })?;

        // Translates statement.
        irgen.translate_stmt(&source.statement.node, &mut context, None, None)?;

        // Creates the end block
        let ret = signature.ret.set_const(false);
        let value = if ret == ir::Dtype::unit() {
            ir::Operand::constant(ir::Constant::unit())
        } else if ret == ir::Dtype::INT {
            // If "main" function, default return value is `0` when return type is `int`
            if name == "main" {
                ir::Operand::constant(ir::Constant::int(0, ret))
            } else {
                ir::Operand::constant(ir::Constant::undef(ret))
            }
        } else {
            ir::Operand::constant(ir::Constant::undef(ret))
        };

        // Last Block of the function
        irgen.insert_block(context, ir::BlockExit::Return { value });

        // Exit variable scope created above
        irgen.exit_scope();

        let func_def = ir::FunctionDefinition {
            allocations: irgen.allocations,
            blocks: irgen.blocks,
            bid_init: irgen.bid_init,
        };

        let decl = self
            .decls
            .get_mut(&name)
            .unwrap_or_else(|| panic!("The declaration of `{name}` must exist"));
        if let ir::Declaration::Function { definition, .. } = decl {
            if definition.is_some() {
                return Err(IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::Misc {
                        message: format!("the name `{name}` is defined multiple time"),
                    },
                ));
            }

            // Update function definition
            *definition = Some(func_def);
        } else {
            panic!("`{name}` must be function declaration")
        }

        Ok(())
    }

    /// Adds a possibly existing declaration.
    ///
    /// Returns error if the previous declearation is incompatible with `decl`.
    fn add_decl(&mut self, name: &str, decl: ir::Declaration) -> Result<(), IrgenError> {
        let Some(old_decl) = self.decls.insert(name.to_string(), decl.clone()) else {
            return Ok(());
        };

        // Check if type is conflicting for pre-declared one
        if !old_decl.is_compatible(&decl) {
            return Err(IrgenError::new(
                name.to_string(),
                IrgenErrorMessage::ConflictingDtype {
                    dtype: old_decl.dtype(),
                    protorype_dtype: decl.dtype(),
                },
            ));
        }

        Ok(())
    }
}

/// Storage for instructions up to the insertion of a block
#[derive(Debug)]
struct Context {
    /// The block id of the current context.
    bid: ir::BlockId,
    /// Current instructions of the block.
    instrs: Vec<Named<Instruction>>,
}

impl Context {
    /// Create a new context with block number bid
    fn new(bid: ir::BlockId) -> Self {
        Self {
            bid,
            instrs: Vec::new(),
        }
    }

    // Adds `instr` to the current context.
    fn insert_instruction(&mut self, instr: Instruction) -> Result<ir::Operand, IrgenErrorMessage> {
        let dtype = instr.dtype();
        self.instrs.push(Named::new(None, instr));

        Ok(ir::Operand::register(
            ir::RegisterId::temp(self.bid, self.instrs.len() - 1),
            dtype,
        ))
    }
}

trait OpExt {
    fn with_load(self, should_load: bool, context: &mut Context) -> ir::Operand;
    fn with_cast(self, target_dtype: &ir::Dtype, context: &mut Context) -> ir::Operand;
}

/// A C function being translated.
struct IrgenFunc<'i> {
    /// return type of the function.
    return_type: ir::Dtype,
    /// initial block id for the function, typically 0.
    bid_init: ir::BlockId,
    /// arguments represented as initial phinodes. Order must be the same of that given in the C
    /// function.
    phinodes_init: Vec<Named<ir::Dtype>>,
    /// local allocations.
    allocations: Vec<Named<ir::Dtype>>,
    /// Map from block id to basic blocks
    blocks: BTreeMap<ir::BlockId, ir::Block>,
    /// current block id. `blocks` must have an entry for all ids less then this
    bid_counter: usize,
    /// current temporary id. Used to create temporary names in the IR for e.g,
    tempid_counter: usize,
    /// Usable definitions
    typedefs: &'i HashMap<String, ir::Dtype>,
    /// Usable structs
    // TODO: Add examples on how to use properly use this field.
    structs: &'i HashMap<String, Option<ir::Dtype>>,
    /// Current symbol table. The initial symbol table has the global variables.
    symbol_table: Vec<HashMap<String, ir::Operand>>,
}

struct LogicNode {
    // entry block id for the current logic subtree
    entry: ir::BlockId,
    // exit block for the current logic subtree
    exit: Context,
    // current value in the exit node
    op: ir::Operand,
}

impl LogicNode {
    fn connect(self, other: Self, irgen_func: &mut IrgenFunc<'_>) -> Self {
        let Self { entry, exit, op } = self;
        let Self {
            entry: entry2,
            exit: exit2,
            op: op2,
        } = other;
        let arg_then = JumpArg::new(ir::BlockId(other.entry.0 - 2), vec![]);
        let arg_else = JumpArg::new(ir::BlockId(other.entry.0 - 1), vec![]);

        irgen_func.insert_block(
            exit,
            ir::BlockExit::ConditionalJump {
                condition: op,
                arg_then,
                arg_else,
            },
        );
        Self {
            entry,
            exit: exit2,
            op: op2,
        }
    }
}

/// type cast: https://en.cppreference.com/w/c/language/conversion.html
/// left value in c:
///     1. identifier: x
///     2. index of array: arr[i]
///     3. member: a->member/a.member
///     4. deref pointer(it could be anything): -> *x
///     5. assignment
///     6. initial value
impl IrgenFunc<'_> {
    /// Allocate a new block id.
    fn alloc_bid(&mut self) -> ir::BlockId {
        let bid = self.bid_counter;
        self.bid_counter += 1;
        ir::BlockId(bid)
    }

    /// Allocate a new temporary id.
    fn alloc_tempid(&mut self) -> String {
        let tempid = self.tempid_counter;
        self.tempid_counter += 1;
        format!("t{tempid}")
    }

    /// Create a new allocation with type given by `alloc`.
    /// we alloc for:
    ///     1. global/local vars
    ///     2. temperal vars during conditional expression evaluation
    ///     3. temperal vars durign logical expression evaluation
    fn insert_alloc(&mut self, alloc: Named<ir::Dtype>) -> ir::RegisterId {
        self.allocations.push(alloc);
        let id = self.allocations.len() - 1;
        ir::RegisterId::local(id)
    }

    /// Insert a new block `context` with exit instruction `exit`.
    ///
    /// # Panic
    ///
    /// Panics if another block with the same bid as `context` already existed.
    fn insert_block(&mut self, context: Context, exit: ir::BlockExit) {
        let block = ir::Block {
            phinodes: if context.bid == self.bid_init {
                self.phinodes_init.clone()
            } else {
                Vec::new()
            },
            instructions: context.instrs,
            exit,
        };
        if self.blocks.insert(context.bid, block).is_some() {
            panic!("the bid `{}` is defined multiple time", context.bid)
        }
    }

    /// utils

    fn find_symbol(&self, name: &str) -> Option<&ir::Operand> {
        for tbl in self.symbol_table.iter().rev() {
            if let Some(v) = tbl.get(name) {
                return Some(v);
            }
        }
        None
    }

    fn find_callee(&self, expr: &Expression) -> Option<ir::Operand> {
        if let Expression::Identifier(id) = expr {
            self.find_symbol(&id.node.name).cloned()
        } else {
            None
        }
    }

    fn current_scope(&self) -> &HashMap<String, ir::Operand> {
        self.symbol_table.last().unwrap()
    }

    fn current_scope_mut(&mut self) -> &mut HashMap<String, ir::Operand> {
        self.symbol_table.last_mut().unwrap()
    }

    // TODO: configurable
    fn size_of_size_t(&self) -> usize {
        32
    }

    fn size_of_pointer(&self) -> usize {
        64
    }

    fn type_of_expr(&self, expr: &Expression) -> Option<ir::Dtype> {
        match expr {
            Expression::Identifier(node) => self
                .find_symbol(&node.node.name)
                .cloned()
                .map(|op| op.dtype()),
            Expression::Constant(node) => {
                ir::Constant::try_from(&node.node).ok().map(|c| c.dtype())
            }
            Expression::UnaryOperator(node) => {
                let op = self.type_of_expr(&node.node.operand.node);
                op.map(|op| match &node.node.operator.node {
                    UnaryOperator::Address => Some(ir::Dtype::pointer(op)),
                    UnaryOperator::Indirection => {
                        if let Some(ptr) = op.get_pointer_inner() {
                            Some(ptr.clone())
                        } else {
                            None
                        }
                    }
                    _ => Some(op),
                })
                .unwrap_or_default()
            }
            Expression::BinaryOperator(node) => {
                let types = self
                    .type_of_expr(&node.node.lhs.node)
                    .zip(self.type_of_expr(&node.node.rhs.node));
                let t = types.and_then(|(t1, t2)| Some(basic_type_promotion(&t1, &t2)));
                t
            }
            _ => unreachable!("invalid or unsupported expr in sizeof, expr:{:?}", expr),
        }
    }

    /// utils end

    /// Enter a scope and create a new symbol table entry, i.e, we are at a `{` in the function.
    fn enter_scope(&mut self) {
        self.symbol_table.push(HashMap::new());
    }

    /// Exit a scope and remove the a oldest symbol table entry. i.e, we are at a `}` in the
    /// function.
    ///
    /// # Panic
    ///
    /// Panics if there are no scopes to exit, i.e, the function has a unmatched `}`.
    fn exit_scope(&mut self) {
        let _unused = self.symbol_table.pop().unwrap();
        debug_assert!(!self.symbol_table.is_empty())
    }

    /// Inserts `var` with `value` to the current symbol table.
    ///
    /// Returns Ok() if the current scope has no previously-stored entry for a given variable.
    fn insert_symbol_table_entry(
        &mut self,
        var: String,
        value: ir::Operand,
    ) -> Result<(), IrgenErrorMessage> {
        let cur_scope = self
            .symbol_table
            .last_mut()
            .expect("symbol table has no valid scope");
        if cur_scope.insert(var.clone(), value).is_some() {
            return Err(IrgenErrorMessage::Redefinition { name: var });
        }

        Ok(())
    }

    // add identifier to current symbol table
    // TODO: merge it with global declration?
    fn translate_local_declaration(
        &mut self,
        source: &Declaration,
        context: &mut Context,
    ) -> Result<(), IrgenError> {
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&source.specifiers).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
        let base_dtype = base_dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("{source:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        // TODO: resolve struct fields
        for init_decl in &source.declarators {
            let declarator = &init_decl.node.declarator.node;
            let name = name_of_declarator(declarator);
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| {
                    IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::InvalidDtype { dtype_error: e },
                    )
                })?
                .deref()
                .clone();
            let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
            if !is_typedef && is_invalid_structure(&dtype, &self.structs) {
                return Err(IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::Misc {
                        message: "incomplete struct type".to_string(),
                    },
                ));
            }

            if is_typedef {
                // Add new typedef if nothing has been declared before
                let prev_dtype = self.typedefs.get(&name).unwrap();

                if prev_dtype != &dtype {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::ConflictingDtype {
                            dtype,
                            protorype_dtype: prev_dtype.clone(),
                        },
                    ));
                }

                continue;
            }

            // Creates a new declaration based on the dtype.
            let mut decl = ir::Declaration::try_from(dtype.clone()).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;

            let dtype = decl.dtype();
            let named = Named::new(Some(name.clone()), dtype.clone());
            let rid = self.insert_alloc(named.clone());
            let ptr = ir::Operand::Register {
                rid,
                dtype: ir::Dtype::pointer(dtype.clone()),
            };
            let _ = self.current_scope_mut().insert(name.clone(), ptr.clone());

            // TODO: is it correct
            if let Some(initializer) = init_decl.node.initializer.as_ref() {
                self.translate_initializor(&dtype, &ptr, &initializer.node, context)?;
            }
        }
        Ok(())
    }

    fn translate_initializor(
        &mut self,
        dtype: &ir::Dtype,
        ptr: &ir::Operand,
        initializer: &Initializer,
        context: &mut Context,
    ) -> Result<(), IrgenError> {
        match &initializer {
            Initializer::Expression(node) => {
                let (op, _) = self.translate_expr(&node.node, false, context)?;
                // assign cast2: initialization
                let op = cast(op, &dtype, context);
                let inst = Instruction::Store {
                    ptr: ptr.clone(),
                    value: op.clone(),
                };
                let _ = context.insert_instruction(inst).unwrap();
            }
            Initializer::List(nodes) => {
                for item in nodes {
                    let dtype = todo!();
                    let ptr = todo!();
                    self.translate_initializor(dtype, ptr, initializer, context)?;
                    // let value = self.translate_expr(&item.node., not_deref, context)
                }
            }
        }
        Ok(())
    }

    /// Transalte a C statement `stmt` under the current block `context`, with `continue` block
    /// `bid_continue` and break block `bid_break`.
    fn translate_stmt(
        &mut self,
        stmt: &Statement,
        context: &mut Context,
        bid_continue: Option<ir::BlockId>,
        bid_break: Option<ir::BlockId>,
    ) -> Result<(), IrgenError> {
        // TODO: enter/leave scope
        match stmt {
            Statement::Labeled(node) => {
                self.translate_stmt(&node.node.statement.node, context, bid_continue, bid_break)?;
            }
            Statement::Compound(vec) => {
                for blockitem in vec {
                    match &blockitem.node {
                        BlockItem::Declaration(node) => {
                            self.translate_local_declaration(&node.node, context)?
                        }
                        BlockItem::Statement(node) => {
                            self.translate_stmt(&node.node, context, bid_continue, bid_break)?
                        }
                        BlockItem::StaticAssert(node) => todo!(),
                    }
                }
            }
            Statement::Expression(node) => {
                if let Some(node) = node {
                    let _ = self.translate_expr(&node.node, false, context)?;
                }
            }

            /// b_before:
            ///     before
            ///     jmp b_cond
            /// b_cond:
            ///     %cond = eval cond
            ///     br %cond b_then, b_else
            /// b_then:
            ///     body
            ///     jmp b_after
            /// b_else:
            ///     Option<body>
            ///     jmp b_after
            /// b_after:
            ///     ...
            Statement::If(node) => {
                let condition = &node.node.condition;
                let (op, _) = self.translate_expr(&condition.node, true, context)?;
                let op = op_to_cond(&node.node.condition.node, op, context);

                let mut ctx_then = Context::new(self.alloc_bid());
                let mut ctx_else = Context::new(self.alloc_bid());
                let mut ctx_after = Context::new(self.alloc_bid());
                let arg_then = JumpArg::new(ctx_then.bid, vec![]);
                let arg_else = JumpArg::new(ctx_else.bid, vec![]);
                let arg_after = JumpArg::new(ctx_after.bid, vec![]);

                // 0. exit current block
                mem::swap(&mut ctx_after, context);
                self.insert_block(
                    ctx_after,
                    ir::BlockExit::ConditionalJump {
                        condition: op,
                        arg_then,
                        arg_else,
                    },
                );

                // 1. then stmt
                self.translate_stmt(
                    &node.node.then_statement.node,
                    &mut ctx_then,
                    bid_continue,
                    bid_break,
                )?;
                self.insert_block(
                    ctx_then,
                    ir::BlockExit::Jump {
                        arg: arg_after.clone(),
                    },
                );

                // 2. else stmt
                if let Some(stmt) = &node.node.else_statement {
                    self.translate_stmt(&stmt.node, &mut ctx_else, bid_continue, bid_break)?;
                }
                self.insert_block(ctx_else, ir::BlockExit::Jump { arg: arg_after });
            }
            /// %expr = eval expr
            /// switch %expr default b_default() [
            ///    x b_x
            ///    y b_y
            /// ]
            /// b_after:
            ///     after
            /// b_x:
            ///     body
            ///     jmp b_after
            /// b_y:
            ///     body
            ///     jmp b_after
            /// b_default:
            ///     body
            ///     jmp b_after
            ///
            /// we only support switch stmt with default case
            /// and all case shall be constant expr
            Statement::Switch(node) => {
                let (op, _) = self.translate_expr(&node.node.expression.node, false, context)?;
                let mut b_after = Context::new(self.alloc_bid());
                let bid_after = b_after.bid;
                let jmp_arg = JumpArg::new(bid_after, vec![]);

                let mut cases = vec![];
                let mut default = None;

                let Statement::Compound(compound) = &node.node.statement.node else {
                    unreachable!("single statement in switch: {:?}", node)
                };
                for blockitem in compound {
                    match &blockitem.node {
                        BlockItem::Statement(node) => {
                            // the bid_break will be used inside the case's stmt
                            // so we need not to insert block here
                            let mut ctx_case = Context::new(self.alloc_bid());
                            let bid = ctx_case.bid;
                            self.translate_stmt(&node.node, &mut ctx_case, bid_continue, None);
                            self.insert_block(
                                ctx_case,
                                ir::BlockExit::Jump {
                                    arg: jmp_arg.clone(),
                                },
                            );
                            // TODO: more robust
                            let Statement::Labeled(label) = &node.node else {
                                unreachable!()
                            };
                            match &label.node.label.node {
                                Label::Identifier(..) | Label::CaseRange(..) => todo!(),
                                Label::Case(node) => {
                                    // we only support constant
                                    let Expression::Constant(constant) = &node.node else {
                                        unreachable!()
                                    };
                                    let c = ir::Constant::try_from(&constant.node).unwrap();
                                    cases.push((c, JumpArg::new(bid, vec![])));
                                }
                                Label::Default => {
                                    default = Some(JumpArg::new(bid, vec![]));
                                }
                            }
                        }
                        _ => unreachable!(),
                    }
                }

                let switch_exit = ir::BlockExit::Switch {
                    value: op,
                    default: default.unwrap(),
                    cases,
                };
                mem::swap(context, &mut b_after);
                self.insert_block(b_after, switch_exit);
                // now active context is in b_after
            }
            /// b_before:
            ///     before
            ///     jmp b_cond
            /// b_cond:
            ///     %expr = eval expr
            ///     br %expr b_body, b_after
            /// b_body:
            ///     body
            ///     jmp b_cond
            /// b_after:
            ///     after
            Statement::While(node) => {
                let mut ctx_cond = Context::new(self.alloc_bid());
                let mut ctx_body = Context::new(self.alloc_bid());
                let mut ctx_after = Context::new(self.alloc_bid());

                let bid_cond = ctx_cond.bid;
                let bid_after = ctx_after.bid;

                let jmp_cond = JumpArg::new(ctx_cond.bid, vec![]);
                let jmp_body = JumpArg::new(ctx_body.bid, vec![]);
                let jmp_after = JumpArg::new(ctx_after.bid, vec![]);

                // 0. finalize current block
                mem::swap(context, &mut ctx_after);
                self.insert_block(
                    ctx_after,
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(bid_cond, vec![]),
                    },
                );

                // 1. cond
                let (op, _) =
                    self.translate_expr(&node.node.expression.node, false, &mut ctx_cond)?;
                let op = op_to_cond(&node.node.expression.node, op, context);
                let exit = ir::BlockExit::ConditionalJump {
                    condition: op,
                    arg_then: jmp_body.clone(),
                    arg_else: jmp_after.clone(),
                };
                self.insert_block(ctx_cond, exit);

                // 2. body
                self.enter_scope();
                self.translate_stmt(
                    &node.node.statement.node,
                    &mut ctx_body,
                    Some(bid_cond),
                    Some(bid_after),
                );
                self.insert_block(
                    ctx_body,
                    ir::BlockExit::Jump {
                        arg: jmp_cond.clone(),
                    },
                );
                self.exit_scope();

                // 3. after, nothing to do, current active context is ctx_after
            }
            /// b_before:
            ///     before
            ///     jmp b_body
            /// b_body:
            ///     body
            ///     jmp b_cond
            /// b_cond:
            ///     %expr = eval expr
            ///     br %expr b_body, b_after
            /// b_after:
            ///     after
            Statement::DoWhile(node) => {
                let mut ctx_body = Context::new(self.alloc_bid());
                let mut ctx_cond = Context::new(self.alloc_bid());
                let mut ctx_after = Context::new(self.alloc_bid());

                let bid_body = ctx_body.bid;
                let bid_cond = ctx_cond.bid;
                let bid_after = ctx_after.bid;

                let jmp_cond = JumpArg::new(ctx_cond.bid, vec![]);
                let jmp_body = JumpArg::new(ctx_body.bid, vec![]);
                let jmp_after = JumpArg::new(ctx_after.bid, vec![]);

                // 0. finalize current block
                mem::swap(context, &mut ctx_after);
                self.insert_block(
                    ctx_after,
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(bid_body, vec![]),
                    },
                );

                // 1. body
                self.enter_scope();
                self.translate_stmt(
                    &node.node.statement.node,
                    &mut ctx_body,
                    Some(bid_body),
                    Some(bid_after),
                );
                self.insert_block(
                    ctx_body,
                    ir::BlockExit::Jump {
                        arg: jmp_cond.clone(),
                    },
                );
                self.exit_scope();

                // 2. cond
                let (op, _) =
                    self.translate_expr(&node.node.expression.node, false, &mut ctx_cond)?;
                let op = op_to_cond(&node.node.expression.node, op, context);
                let exit = ir::BlockExit::ConditionalJump {
                    condition: op,
                    arg_then: jmp_body.clone(),
                    arg_else: jmp_after.clone(),
                };
                self.insert_block(ctx_cond, exit);

                // 3. after, nothing to do, current active context is ctx_after
            }
            /// b_before:
            ///     before
            ///     jmp b_init
            /// b_init:
            ///     initializer
            ///     jmp b_cond
            /// b_cond:
            ///     %cond = eval cond
            ///     br %cond b_body, b_after
            /// b_body:
            ///     body
            ///     jmp b_step
            /// b_step:
            ///     step
            ///     jmp b_cond
            /// b_after:
            ///     after
            Statement::For(node) => {
                self.enter_scope();

                let mut ctx_init = Context::new(self.alloc_bid());
                let mut ctx_cond = Context::new(self.alloc_bid());
                let mut ctx_body = Context::new(self.alloc_bid());
                let mut ctx_step = Context::new(self.alloc_bid());
                let mut ctx_after = Context::new(self.alloc_bid());
                let bid_after = ctx_after.bid;

                let jmp_cond = JumpArg::new(ctx_cond.bid, vec![]);
                let jmp_body = JumpArg::new(ctx_body.bid, vec![]);
                let jmp_after = JumpArg::new(ctx_after.bid, vec![]);
                let jmp_step = JumpArg::new(ctx_step.bid, vec![]);
                let jmp_after = JumpArg::new(ctx_after.bid, vec![]);

                // 0. freeze current block
                mem::swap(context, &mut ctx_after);
                self.insert_block(
                    ctx_after,
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(ctx_init.bid, vec![]),
                    },
                );
                // 1. initializer
                match &node.node.initializer.node {
                    ForInitializer::Empty => {}
                    ForInitializer::Expression(node) => {
                        // should not load the value
                        let _ = self.translate_expr(&node.node, true, &mut ctx_init)?;
                    }
                    ForInitializer::Declaration(node) => {
                        self.translate_local_declaration(&node.node, &mut ctx_init)?;
                    }
                    ForInitializer::StaticAssert(node) => todo!(),
                }
                self.insert_block(
                    ctx_init,
                    ir::BlockExit::Jump {
                        arg: jmp_cond.clone(),
                    },
                );

                // 2. cond
                if let Some(cond) = &node.node.condition {
                    let (op, _) = self.translate_expr(&cond.node, true, &mut ctx_cond)?;
                    let op = op_to_cond(&cond.node, op, context);
                    let exit = ir::BlockExit::ConditionalJump {
                        condition: op,
                        arg_then: jmp_body.clone(),
                        arg_else: jmp_after.clone(),
                    };
                    self.insert_block(ctx_cond, exit);
                } else {
                    self.insert_block(
                        ctx_cond,
                        ir::BlockExit::Jump {
                            arg: jmp_body.clone(),
                        },
                    );
                }

                // 3. body
                self.enter_scope();
                self.translate_stmt(
                    &node.node.statement.node,
                    &mut ctx_body,
                    Some(ctx_step.bid),
                    Some(bid_after),
                );
                self.insert_block(
                    ctx_body,
                    ir::BlockExit::Jump {
                        arg: jmp_step.clone(),
                    },
                );
                self.exit_scope();

                // 4. step
                if let Some(step) = &node.node.step {
                    // discard
                    let _ = self.translate_expr(&step.node, false, &mut ctx_step)?;
                }
                self.insert_block(
                    ctx_step,
                    ir::BlockExit::Jump {
                        arg: jmp_cond.clone(),
                    },
                );
                self.exit_scope();

                // 5. after, nothing to do, since the active context is now ctx_after now
            }
            Statement::Goto(node) => todo!(),
            Statement::Continue => {
                if let Some(c) = bid_continue {
                    let mut new_context = Context::new(self.alloc_bid());
                    mem::swap(&mut new_context, context);
                    let jmp_continue = JumpArg::new(c, vec![]);
                    self.insert_block(new_context, ir::BlockExit::Jump { arg: jmp_continue });
                }
            }
            Statement::Break => {
                if let Some(b) = bid_break {
                    let mut new_context = Context::new(self.alloc_bid());
                    mem::swap(&mut new_context, context);
                    let jmp_break = JumpArg::new(b, vec![]);
                    self.insert_block(new_context, ir::BlockExit::Jump { arg: jmp_break });
                }
            }
            Statement::Return(node) => {
                if let Some(node) = node {
                    let (op, _) = self.translate_expr(&node.node, false, context)?;
                    let return_type = self.return_type.clone();
                    // assign cast4: return
                    let value = cast(op, &return_type, context);

                    let mut new_context = Context::new(self.alloc_bid());
                    mem::swap(&mut new_context, context);
                    self.insert_block(new_context, ir::BlockExit::Return { value });
                }
            }
            Statement::Asm(node) => todo!(),
        }
        Ok(())
    }

    // TODO: logical or
    fn translate_logic_expr(
        &mut self,
        collects: &[&Expression],
        operators: &[BinaryOperator],
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenError> {
        debug_assert!(
            operators
                .iter()
                .all(|op| [BinaryOperator::LogicalOr, BinaryOperator::LogicalAnd].contains(op))
        );
        assert_eq!(collects.len(), operators.len() + 1);
        let dtype = ir::Dtype::BOOL;
        let mut tmps = vec![];
        for i in 0..operators.len() {
            let name = self.alloc_tempid();
            let named = Named::new(Some(name.clone()), dtype.clone());
            let rid = self.insert_alloc(named.clone());
            let ptr = ir::Operand::Register {
                rid,
                dtype: ir::Dtype::pointer(dtype.clone()),
            };
            tmps.push(ptr);
        }
        // will skip the first expression

        // we generate the logical tree in the following order
        //       and
        //      /   \
        //     and  z
        //     /\
        //    x  y
        // then the order is z1, z2, z3, y1, y2, y3
        // and z3 is the exit node,
        // x is the entry expression(we will not generate node for this expr)

        let mut exit_info = None;
        let mut next_jmp = None;
        for ((ptr, op), expr) in tmps
            .into_iter()
            .rev()
            .zip(operators.iter().rev())
            .zip(collects.iter().rev())
        {
            let mut c1 = Context::new(self.alloc_bid());
            let mut c2 = Context::new(self.alloc_bid());
            let mut c3 = Context::new(self.alloc_bid());
            let bid1 = c1.bid;
            let jmp_v3 = JumpArg::new(c3.bid, vec![]);

            if op == &BinaryOperator::LogicalAnd {
                let (op, _) = self.translate_expr(expr, false, &mut c1)?;
                let op = cast(op, &dtype, &mut c1);
                c1.insert_instruction(Instruction::Store {
                    ptr: ptr.clone(),
                    value: op,
                });

                let zero = ir::Operand::constant(ir::Constant::ZERO_U1);
                c2.insert_instruction(Instruction::Store {
                    ptr: ptr.clone(),
                    value: zero,
                });
            } else {
                let one = ir::Operand::constant(ir::Constant::ONE_U1);
                c1.insert_instruction(Instruction::Store {
                    ptr: ptr.clone(),
                    value: one,
                });

                let (op, _) = self.translate_expr(expr, false, &mut c2)?;
                let op = cast(op, &dtype, &mut c2);
                c2.insert_instruction(Instruction::Store {
                    ptr: ptr.clone(),
                    value: op,
                });
            }

            self.insert_block(
                c1,
                ir::BlockExit::Jump {
                    arg: jmp_v3.clone(),
                },
            );
            self.insert_block(
                c2,
                ir::BlockExit::Jump {
                    arg: jmp_v3.clone(),
                },
            );

            let op = c3
                .insert_instruction(Instruction::Load { ptr: ptr.clone() })
                .unwrap();

            match next_jmp.clone() {
                Some(jmp) => {
                    let arg_then = JumpArg::new(ir::BlockId(jmp), vec![]);
                    let arg_else = JumpArg::new(ir::BlockId(jmp + 1), vec![]);

                    self.insert_block(
                        c3,
                        ir::BlockExit::ConditionalJump {
                            condition: op,
                            arg_then,
                            arg_else,
                        },
                    );
                }
                None => {
                    exit_info = Some((c3, op));
                }
            }

            next_jmp = Some(bid1.0);
        }

        // now evaluate the first expr, and switch to exit_block

        let jmp = next_jmp.unwrap();
        let (mut exit, op) = exit_info.unwrap();
        let (lhs, _) = self.translate_expr(collects[0], false, context)?;
        let lhs = cast(lhs, &ir::Dtype::BOOL, context);
        mem::swap(context, &mut exit);
        let arg_then = JumpArg::new(ir::BlockId(jmp), vec![]);
        let arg_else = JumpArg::new(ir::BlockId(jmp + 1), vec![]);
        self.insert_block(
            exit,
            ir::BlockExit::ConditionalJump {
                condition: lhs,
                arg_then,
                arg_else,
            },
        );
        Ok(op)
    }

    // lvalue in unary operator:
    //      4. deref pointer(it could be anything): -> *x
    fn translate_unary_expr(
        &mut self,
        expr: &UnaryOperatorExpression,
        no_deref: bool,
        context: &mut Context,
    ) -> Result<(ir::Operand, Option<ir::Operand>), IrgenError> {
        let (op, ptr) = if let Some((is_pre, bin_op)) = is_unary_assign(&expr.operator.node) {
            // a++, a--, ++a, --a
            // we need lvalue here
            // TODO: can we handle pointer++
            let (op, lvalue) = self.translate_expr(&expr.operand.node, false, context)?;
            let dtype = op.dtype();
            let op_after_update = context
                .insert_instruction(Instruction::BinOp {
                    op: bin_op,
                    lhs: op.clone(),
                    rhs: ir::Operand::Constant(ir::Constant::int(1, dtype.clone())),
                    dtype: dtype.clone(),
                })
                .unwrap();
            let _ = context.insert_instruction(Instruction::Store {
                ptr: lvalue.unwrap(),
                value: op_after_update.clone(),
            });
            (if is_pre { op_after_update } else { op }, None)
        } else {
            match &expr.operator.node {
                UnaryOperator::Address => {
                    // int a; int* p = &a;
                    // will return the pointer to the var
                    // TODO: error handling
                    let (op, _) = self.translate_expr(&expr.operand.node, true, context)?;
                    (op.clone(), None)
                }
                UnaryOperator::Indirection => {
                    // int a; int* p = &a; *p = 1;
                    // TODO: fuck this shit
                    let (op, lvalue) = self.translate_expr(&expr.operand.node, true, context)?;
                    let value = load_direct(op.clone(), lvalue.is_some(), context);
                    if no_deref {
                        (value.clone(), Some(op))
                    } else {
                        let orig_value = value;
                        let value = load_direct(orig_value.clone(), true, context);
                        (value, Some(orig_value))
                    }
                }
                _ => {
                    // others are not left value
                    let (op, _) = self.translate_expr(&expr.operand.node, false, context)?;
                    let dtype = op.dtype();
                    let inst = Instruction::UnaryOp {
                        op: expr.operator.node.clone(),
                        operand: op,
                        dtype,
                    };
                    (context.insert_instruction(inst).unwrap(), None)
                }
            }
        };
        Ok((op, ptr))
    }

    fn translate_binary_expr(
        &mut self,
        orig_expr: &Expression, // TODO: consider remove this
        expr: &BinaryOperatorExpression,
        no_deref: bool,
        context: &mut Context,
    ) -> Result<(ir::Operand, Option<ir::Operand>), IrgenError> {
        // both lhs and rhs might be a local allocation
        // use the `maybe_load_local` instead of `translate_expr` result

        /// if node's operator is +=, -=, *=, then transform into the corresponding
        /// more and insert the following extra instructions:
        /// lhs += rhs:
        ///      %1 = add lhs rhs
        ///      %2 = store %1
        ///
        /// should return %2
        let mut ptr = None;
        let op = if let Some(assign_op) = assign_binop(&expr.operator.node) {
            let (lhs, lvalue) = self.translate_expr(&expr.lhs.node, false, context)?;
            let (rhs, _) = self.translate_expr(&expr.rhs.node, false, context)?;
            let lvalue = lvalue.unwrap();
            let dtype = lhs.dtype();
            // let dtype = dtype_ptr.get_pointer_inner().cloned().unwrap();
            // assign cast1: assignment operator
            let rhs = cast(rhs, &dtype, context);
            // %1
            let compute = Instruction::BinOp {
                op: assign_op,
                lhs,
                rhs,
                dtype,
            };
            // %2
            let op2 = context.insert_instruction(compute).unwrap();
            let _ = context.insert_instruction(Instruction::Store {
                ptr: lvalue,
                value: op2.clone(),
            });
            op2
        } else {
            match &expr.operator.node {
                BinaryOperator::Assign => {
                    // int *p = &a;
                    // *p = 1;
                    let (lhs, _) = self.translate_expr(&expr.lhs.node, true, context)?;
                    let (rhs, _) = self.translate_expr(&expr.rhs.node, false, context)?;
                    let dtype_ptr = lhs.dtype();
                    let dtype = dtype_ptr.get_pointer_inner().cloned().unwrap_or(dtype_ptr);
                    let rhs = cast(rhs, &dtype, context);
                    let _ = context.insert_instruction(Instruction::Store {
                        ptr: lhs,
                        value: rhs.clone(),
                    });
                    rhs
                }
                BinaryOperator::Index => {
                    let (lhs, _) = self.translate_expr(&expr.lhs.node, false, context)?;
                    let (rhs, _) = self.translate_expr(&expr.rhs.node, false, context)?;
                    let index_dtype = ir::Dtype::int(64);
                    let rhs = cast(rhs, &index_dtype, context);

                    // dtype is a pointer to array
                    let dtype = lhs.dtype();

                    let (size, _) = dtype.index_dtype().size_align_of(self.structs).unwrap();
                    let c = ir::Constant::int(size as _, ir::Dtype::int(64));
                    let mul = Instruction::BinOp {
                        op: BinaryOperator::Multiply,
                        lhs: rhs,
                        rhs: ir::Operand::constant(c),
                        dtype: index_dtype,
                    };
                    let rhs = context.insert_instruction(mul).unwrap();

                    let inst = Instruction::GetElementPtr {
                        ptr: lhs,
                        offset: rhs,
                        dtype,
                    };

                    let op = context.insert_instruction(inst).unwrap();
                    let array_type = op.dtype().get_pointer_inner().cloned().unwrap();
                    if no_deref {
                        op
                    } else {
                        // we are evaluating index expr, and no_deref is false,
                        // so we should treat op as an ptr and load it (if it's not an array type)
                        flatten_array(op, &array_type, context, true)
                    }
                }
                BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr => {
                    let mut leaf_nodes = vec![];
                    let mut operators = vec![];
                    collect_logic_leaf_expr(orig_expr, &mut leaf_nodes, &mut operators);
                    self.translate_logic_expr(&leaf_nodes, &operators, context)?
                }
                _ => {
                    let (lhs, ..) = self.translate_expr(&expr.lhs.node, false, context)?;
                    let (rhs, _) = self.translate_expr(&expr.rhs.node, false, context)?;
                    let (operand_dtype, result_dtype) = lhs
                        .dtype()
                        .binop_dtype(&rhs.dtype(), &expr.operator.node)
                        .unwrap();

                    let lhs = cast(lhs, &operand_dtype, context);
                    let rhs = cast(rhs, &operand_dtype, context);
                    // let dtype = binop_dtype(&operand_dtype, &expr.operator.node);

                    let inst = Instruction::BinOp {
                        op: expr.operator.node.clone(),
                        lhs,
                        rhs,
                        dtype: result_dtype,
                    };
                    context.insert_instruction(inst).unwrap()
                }
            }
        };
        Ok((op, ptr))
    }

    /// left value in expr:
    ///     1. identifier: x   -- expr
    ///     2. index of array: arr[i]  -- binary
    ///     3. member: a->member/a.member -- binary
    ///     4. deref pointer(it could be anything): -> *x  -- unary
    ///     5. assignment -- unary + binary
    ///     6. initial value -- todo!()
    fn translate_expr(
        &mut self,
        expr: &Expression,
        no_deref: bool,
        context: &mut Context,
    ) -> Result<(ir::Operand, Option<ir::Operand>), IrgenError> {
        // TODO: conditional expr
        let (op, ptr) = match expr {
            Expression::Identifier(node) => {
                let op = self.find_symbol(&node.node.name).cloned().expect(&format!(
                    "{}, symbol table: {:?}",
                    json!(expr),
                    self.symbol_table
                ));
                // TODO: when shall we load the value from allocation?
                // if it's the first access of the function argument
                // store the value from function arg to local allocation slot
                let should_load = !no_deref && (op.is_global() || op.is_alloc() || op.is_arg());
                (load_direct(op.clone(), should_load, context), Some(op))
            }
            Expression::Constant(node) => (
                ir::Operand::constant(ir::Constant::try_from(&node.node).unwrap()),
                None,
            ),
            /// if it's ++ or --, then do the following transform and return
            /// the correct operand by it's pre/post semantic
            /// x = ++i =>
            ///       %expr
            ///       %1 = add %expr 1
            ///       %2 = store %1 i
            /// should return %1
            ///
            /// y = i++ =>
            ///       %expr
            ///       %1 = add i 1
            ///       %2 = store %1 i
            /// should return %expr
            ///
            /// TODO: type cast
            Expression::UnaryOperator(node) => {
                self.translate_unary_expr(&node.node, no_deref, context)?
            }
            /// TODO: type cast
            /// TODO: logical expression evaluation
            ///
            /// if is assign (can be = or ++), then lhs must be a pointer, rhs must be a value
            /// if not, then lhs and rhs are both values
            Expression::BinaryOperator(node) => {
                self.translate_binary_expr(expr, &node.node, no_deref, context)?
            }
            Expression::Member(node) => {
                // TODO: make it readable
                let (struct_ptr, _) =
                    self.translate_expr(&node.node.expression.node, true, context)?;
                let member = node.node.identifier.node.name.clone();
                let dtype = struct_ptr.dtype();
                let struct_dtype = dtype.get_pointer_inner().unwrap();
                let struct_name = struct_dtype.get_struct_name().unwrap().clone().unwrap();
                let struct_real_dtype = self.structs.get(&struct_name).unwrap().clone().unwrap();
                let (offset, dtype) = struct_real_dtype
                    .resolve_struct_field_offset(member.as_str(), self.structs)
                    .unwrap();
                let offset =
                    ir::Operand::constant(ir::Constant::int(offset as _, ir::Dtype::int(64)));
                let dtype = ir::Dtype::pointer(dtype);
                let inst = Instruction::GetElementPtr {
                    ptr: struct_ptr,
                    offset,
                    dtype: dtype.clone(),
                };
                let op = context.insert_instruction(inst).unwrap();
                // should return ptr rather than the loaded value
                (
                    flatten_array(
                        op.clone(),
                        dtype.get_pointer_inner().unwrap(),
                        context,
                        false,
                    ),
                    Some(op),
                )
            }
            Expression::Call(node) => {
                // TODO: if callee is a function pointer
                // callee can be either
                // 1. a global variable of function
                // 2. a function pointer
                let (callee, _) = self.translate_expr(&node.node.callee.node, true, context)?;
                let mut dtype = callee.dtype();
                if let Some(inner) = dtype.get_pointer_inner() {
                    dtype = inner.clone()
                };

                let op = if let ir::Dtype::Function { ret, params } = &dtype {
                    let mut args = vec![];
                    assert_eq!(params.len(), node.node.arguments.len());
                    for (expr, target_dtype) in node.node.arguments.iter().zip(params) {
                        let (op, _) = self.translate_expr(&expr.node, false, context)?;
                        // assign cast3: function call
                        let op = cast(op, target_dtype, context);
                        args.push(op);
                    }

                    let inst = Instruction::Call {
                        callee: callee.clone(),
                        args,
                        return_type: *ret.clone(),
                    };
                    context.insert_instruction(inst).unwrap()
                } else {
                    unreachable!("{callee:?}")
                };
                (op, None)
            }
            Expression::SizeOfTy(node) => {
                let tname = node
                    .node
                    .0
                    .node
                    .specifiers
                    .iter()
                    .filter_map(|spec| {
                        if let SpecifierQualifier::TypeSpecifier(spec) = &spec.node {
                            type_size(&spec.node)
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                assert_eq!(tname.len(), 1);
                (
                    ir::Operand::constant(ir::Constant::int(
                        tname[0] as _,
                        ir::Dtype::int(64).signed(false),
                    )),
                    None,
                )
            }
            Expression::SizeOfVal(node) => {
                let dtype = self.type_of_expr(&node.node.0.node).unwrap();
                let (size, _) = dtype.size_align_of(&self.structs).unwrap();
                (
                    ir::Operand::constant(ir::Constant::int(
                        size as _,
                        ir::Dtype::int(64).signed(false),
                    )),
                    None,
                )
            }
            Expression::AlignOf(node) => {
                let tname = node
                    .node
                    .0
                    .node
                    .specifiers
                    .iter()
                    .filter_map(|spec| {
                        if let SpecifierQualifier::TypeSpecifier(spec) = &spec.node {
                            type_align(&spec.node)
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                assert_eq!(tname.len(), 1);
                let dtype = ir::Dtype::int(64).signed(false);
                (
                    ir::Operand::constant(ir::Constant::int(tname[0] as _, dtype)),
                    None,
                )
            }
            Expression::Cast(node) => {
                let (op, _) = self.translate_expr(&node.node.expression.node, false, context)?;
                // TODO: resolve struct and typedef types
                let dtype = ir::Dtype::try_from(&node.node.type_name.node).unwrap();
                let op = cast(op, &dtype, context);
                // ptr = Some(op.clone());
                (op, None)
            }
            /// b_before:
            ///     before
            ///     br %expr b_then, b_else
            /// b_then:
            ///     store %then_expr tmp
            ///     jmp b_after
            /// b_else:
            ///     store %else_expr tmp
            ///     jmp b_after
            /// b_after:
            ///     after
            Expression::Conditional(node) => {
                let (op, _) = self.translate_expr(&node.node.condition.node, false, context)?;
                let op = op_to_cond(&node.node.condition.node, op, context);

                let mut ctx_then = Context::new(self.alloc_bid());
                let mut ctx_else = Context::new(self.alloc_bid());
                let mut ctx_after = Context::new(self.alloc_bid());
                let bid_then = ctx_then.bid;
                let bid_else = ctx_else.bid;
                let bid_after = ctx_after.bid;
                let arg_then = JumpArg::new(bid_then, vec![]);
                let arg_else = JumpArg::new(bid_else, vec![]);
                let arg_after = JumpArg::new(bid_after, vec![]);

                mem::swap(context, &mut ctx_after);

                // 0. finalize current block
                self.insert_block(
                    ctx_after,
                    ir::BlockExit::ConditionalJump {
                        condition: op,
                        arg_then,
                        arg_else,
                    },
                );

                // 1.1 then expr
                let (op, _) =
                    self.translate_expr(&node.node.then_expression.node, false, &mut ctx_then)?;
                let dtype = op.dtype();

                // -1. delay the temp value allocation until we know the concrete type
                let named = Named::new(Some(self.alloc_tempid()), dtype.clone());
                let rid = self.insert_alloc(named.clone());
                let ptr = ir::Operand::Register {
                    rid,
                    dtype: ir::Dtype::pointer(dtype.clone()),
                };
                let _ = self
                    .current_scope_mut()
                    .insert(named.name().cloned().unwrap(), ptr.clone());

                // 1.2 then expr
                let store1 = Instruction::Store {
                    ptr: ptr.clone(),
                    value: op,
                };
                ctx_then.insert_instruction(store1);
                self.insert_block(
                    ctx_then,
                    ir::BlockExit::Jump {
                        arg: arg_after.clone(),
                    },
                );

                // 2. else expr
                let (op, _) =
                    self.translate_expr(&node.node.else_expression.node, false, &mut ctx_else)?;
                // TODO: doe we need to cast type here?
                let store1 = Instruction::Store {
                    ptr: ptr.clone(),
                    value: op,
                };
                ctx_else.insert_instruction(store1);
                self.insert_block(
                    ctx_else,
                    ir::BlockExit::Jump {
                        arg: arg_after.clone(),
                    },
                );

                // 3. now the active context is ctx_after
                //    return the load of the temp value as the return result of the whole conditional expr
                (load_direct(ptr.clone(), !no_deref, context), Some(ptr))
            }
            Expression::Comma(vec) => {
                let mut op = None;
                for expr in vec.iter() {
                    op = Some(self.translate_expr(&expr.node, false, context)?.0);
                }
                (op.unwrap(), None)
            }
            Expression::CompoundLiteral(..) => todo!(),
            Expression::Statement(..) => todo!(),
            Expression::StringLiteral(..) => todo!(),
            Expression::GenericSelection(..) => todo!(),
            Expression::OffsetOf(..) => todo!(),
            Expression::VaArg(..) => todo!(),
        };

        Ok((op, ptr))
    }

    /// Translate initial parameter declarations of the functions to IR.
    ///
    /// For example, given the following C function from [`foo.c`][foo]:
    ///
    /// ```C
    /// int foo(int x, int y, int z) {
    ///    if (x == y) {
    ///       return y;
    ///    } else {
    ///       return z;
    ///    }
    /// }
    /// ```
    ///
    /// The IR before this function looks roughly as follows:
    ///
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    ///   ...
    /// ```
    ///
    /// With the following arguments :
    ///
    /// ```ignore
    /// signature = FunctionSignature { ret: ir::INT, params: vec![ir::INT, ir::INT, ir::INT] }
    /// bid_init = 0
    /// name_of_params = ["x", "y", "z"]
    /// context = // omitted
    /// ```
    ///
    /// The resulting IR after this function should be roughly follows :
    ///
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///       %l0:i32:x
    ///       %l1:i32:y
    ///       %l2:i32:z
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    ///     %b0:i0:unit = store %b0:p0:i32 %l0:i32*
    ///     %b0:i1:unit = store %b0:p1:i32 %l1:i32*
    ///     %b0:i2:unit = store %b0:p2:i32 %l2:i32*
    ///   ...
    /// ```
    ///
    /// In particular, note that it is added to the local allocation list and store them to the
    /// initial phinodes.
    ///
    /// Note that the resulting IR is **a** solution. If you can think of a better way to
    /// translate parameters, feel free to do so.
    ///
    /// [foo]: https://github.com/kaist-cp/kecc-public/blob/main/examples/c/foo.c
    fn translate_parameter_decl(
        &mut self,
        signature: &ir::FunctionSignature,
        bid_init: ir::BlockId,
        name_of_params: &[String],
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        for (idx, (name, t)) in name_of_params
            .iter()
            .zip(signature.params.iter())
            .enumerate()
        {
            let named = Named::new(Some(name.into()), t.clone());
            // alloc
            let rid = self.insert_alloc(named.clone());
            let ptr = ir::Operand::Register {
                rid,
                dtype: ir::Dtype::pointer(t.clone()),
            };
            let value = ir::Operand::Register {
                rid: ir::RegisterId::arg(bid_init.clone(), idx),
                dtype: t.clone(),
            };
            // no need to cast
            let inst = Instruction::Store {
                ptr: ptr.clone(),
                value: value.clone(),
            };
            let op = context.insert_instruction(inst).unwrap();
            let _ = self.current_scope_mut().insert(name.clone(), ptr.clone());
            self.phinodes_init.push(named);
        }

        Ok(())
    }
}

struct ExprResult {
    result: ir::Operand,
    ptr: Option<ir::Operand>,
}

#[inline]
fn name_of_declarator(declarator: &Declarator) -> String {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(identifier) => identifier.node.name.clone(),
        DeclaratorKind::Declarator(declarator) => name_of_declarator(&declarator.node),
    }
}

#[inline]
fn name_of_params_from_function_declarator(declarator: &Declarator) -> Option<Vec<String>> {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(_) => {
            name_of_params_from_derived_declarators(&declarator.derived)
        }
        DeclaratorKind::Declarator(next_declarator) => {
            name_of_params_from_function_declarator(&next_declarator.node)
                .or_else(|| name_of_params_from_derived_declarators(&declarator.derived))
        }
    }
}

#[inline]
fn name_of_params_from_derived_declarators(
    derived_decls: &[Node<DerivedDeclarator>],
) -> Option<Vec<String>> {
    for derived_decl in derived_decls {
        match &derived_decl.node {
            DerivedDeclarator::Function(func_decl) => {
                let name_of_params = func_decl
                    .node
                    .parameters
                    .iter()
                    .map(|p| name_of_parameter_declaration(&p.node))
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                return Some(name_of_params);
            }
            DerivedDeclarator::KRFunction(_kr_func_decl) => {
                // K&R function is allowed only when it has no parameter
                return Some(Vec::new());
            }
            _ => (),
        };
    }

    None
}

#[inline]
fn name_of_parameter_declaration(parameter_declaration: &ParameterDeclaration) -> Option<String> {
    let declarator = parameter_declaration.declarator.as_ref()?;
    Some(name_of_declarator(&declarator.node))
}

#[inline]
fn is_valid_initializer(
    initializer: &Initializer,
    dtype: &ir::Dtype,
    structs: &HashMap<String, Option<ir::Dtype>>,
) -> bool {
    match initializer {
        Initializer::Expression(expr) => match dtype {
            ir::Dtype::Int { .. } | ir::Dtype::Float { .. } | ir::Dtype::Pointer { .. } => {
                match &expr.node {
                    Expression::Constant(_) => true,
                    Expression::UnaryOperator(unary) => matches!(
                        &unary.node.operator.node,
                        UnaryOperator::Minus | UnaryOperator::Plus
                    ),
                    _ => false,
                }
            }
            _ => false,
        },
        Initializer::List(items) => match dtype {
            ir::Dtype::Array { inner, .. } => items
                .iter()
                .all(|i| is_valid_initializer(&i.node.initializer.node, inner, structs)),
            ir::Dtype::Struct { name, .. } => {
                let name = name.as_ref().expect("struct should have its name");
                let struct_type = structs
                    .get(name)
                    .expect("struct type matched with `name` must exist")
                    .as_ref()
                    .expect("`struct_type` must have its definition");
                let fields = struct_type
                    .get_struct_fields()
                    .expect("`struct_type` must be struct type")
                    .as_ref()
                    .expect("`fields` must be `Some`");

                izip!(fields, items).all(|(f, i)| {
                    is_valid_initializer(&i.node.initializer.node, f.deref(), structs)
                })
            }
            _ => false,
        },
    }
}

#[inline]
fn is_invalid_structure(dtype: &ir::Dtype, structs: &HashMap<String, Option<ir::Dtype>>) -> bool {
    // When `dtype` is `Dtype::Struct`, `structs` has real definition of `dtype`
    if let ir::Dtype::Struct { name, fields, .. } = dtype {
        assert!(name.is_some() && fields.is_none());
        let name = name.as_ref().unwrap();
        structs.get(name).is_none_or(Option::is_none)
    } else {
        false
    }
}

fn assign_binop(op: &BinaryOperator) -> Option<BinaryOperator> {
    match op {
        BinaryOperator::AssignMultiply => Some(BinaryOperator::Multiply),
        BinaryOperator::AssignDivide => Some(BinaryOperator::Divide),
        BinaryOperator::AssignModulo => Some(BinaryOperator::Modulo),
        BinaryOperator::AssignPlus => Some(BinaryOperator::Plus),
        BinaryOperator::AssignMinus => Some(BinaryOperator::Minus),
        BinaryOperator::AssignShiftLeft => Some(BinaryOperator::ShiftLeft),
        BinaryOperator::AssignShiftRight => Some(BinaryOperator::ShiftRight),
        BinaryOperator::AssignBitwiseAnd => Some(BinaryOperator::BitwiseAnd),
        BinaryOperator::AssignBitwiseXor => Some(BinaryOperator::BitwiseXor),
        BinaryOperator::AssignBitwiseOr => Some(BinaryOperator::BitwiseOr),
        _ => None,
    }
}

// returns: (if its's a self assign pre operator, the corresponding bin op)
fn is_unary_assign(op: &UnaryOperator) -> Option<(bool, BinaryOperator)> {
    match op {
        UnaryOperator::PreIncrement => Some((true, BinaryOperator::Plus)),
        UnaryOperator::PreDecrement => Some((true, BinaryOperator::Minus)),
        UnaryOperator::PostIncrement => Some((false, BinaryOperator::Plus)),
        UnaryOperator::PostDecrement => Some((false, BinaryOperator::Minus)),
        _ => None,
    }
}

fn identifier(expr: &Expression) -> Option<String> {
    if let Expression::Identifier(id) = expr {
        Some(id.node.name.clone())
    } else {
        None
    }
}

fn load_direct(ptr: ir::Operand, should_load: bool, context: &mut Context) -> ir::Operand {
    if should_load {
        let load = Instruction::Load { ptr };
        context.insert_instruction(load).unwrap()
    } else {
        ptr
    }
}

fn cast(orig: ir::Operand, target_dtype: &ir::Dtype, context: &mut Context) -> ir::Operand {
    if orig.dtype() == *target_dtype {
        orig
    } else {
        let cast_inst = Instruction::TypeCast {
            value: orig,
            target_dtype: target_dtype.clone(),
        };
        context.insert_instruction(cast_inst).unwrap()
    }
}

fn op_to_cond(expr: &Expression, orig: ir::Operand, context: &mut Context) -> ir::Operand {
    // 1. cast to int first
    let op = if !matches!(orig.dtype(), ir::Dtype::Int { .. }) {
        cast(orig, &ir::Dtype::int(32), context)
    } else {
        orig
    };

    // 2. cmp with int zero(of the same width)
    if let ir::Dtype::Int { width, .. } = op.dtype()
        && width != 1
    {
        let zero = ir::Constant::int(0, ir::Dtype::int(width));
        let cmp = Instruction::BinOp {
            op: BinaryOperator::NotEquals,
            lhs: op,
            rhs: ir::Operand::constant(zero),
            dtype: ir::Dtype::BOOL,
        };
        context.insert_instruction(cmp).unwrap()
    } else {
        op
    }
}

fn is_simple_expr(expr: &Expression) -> bool {
    match expr {
        Expression::Identifier(..)
        | Expression::Constant(..)
        | Expression::StringLiteral(..)
        | Expression::SizeOfTy(..)
        | Expression::SizeOfVal(..)
        | Expression::AlignOf(..)
        | Expression::Comma(..)
        | Expression::OffsetOf(..) => true,
        _ => false,
    }
}

fn binop_dtype(operand_dtype: &ir::Dtype, operator: &BinaryOperator) -> ir::Dtype {
    match operator {
        BinaryOperator::Less
        | BinaryOperator::Greater
        | BinaryOperator::LessOrEqual
        | BinaryOperator::GreaterOrEqual
        | BinaryOperator::Equals
        | BinaryOperator::NotEquals => ir::Dtype::BOOL,

        // arithmatic
        BinaryOperator::Multiply
        | BinaryOperator::Divide
        | BinaryOperator::Modulo
        | BinaryOperator::Plus
        | BinaryOperator::Minus
        | BinaryOperator::ShiftLeft
        | BinaryOperator::ShiftRight
        | BinaryOperator::AssignMultiply
        | BinaryOperator::AssignDivide
        | BinaryOperator::AssignModulo
        | BinaryOperator::AssignPlus
        | BinaryOperator::AssignMinus
        | BinaryOperator::AssignShiftLeft
        | BinaryOperator::AssignShiftRight
        | BinaryOperator::AssignBitwiseAnd
        | BinaryOperator::AssignBitwiseXor
        | BinaryOperator::AssignBitwiseOr => operand_dtype.clone(),

        BinaryOperator::BitwiseAnd | BinaryOperator::BitwiseXor | BinaryOperator::BitwiseOr => {
            ir::Dtype::int(32)
        }

        BinaryOperator::Assign => ir::Dtype::unit(),

        // should not be called
        BinaryOperator::Index => todo!(),
        BinaryOperator::LogicalAnd => todo!(),
        BinaryOperator::LogicalOr => todo!(),
    }
}

fn flatten_array(
    op: ir::Operand,
    array_type: &ir::Dtype,
    context: &mut Context,
    should_load: bool,
) -> ir::Operand {
    if let ir::Dtype::Array { inner, .. } = array_type {
        // TODO: why is here i32 rather than i64 in `GetElementPtr` inst in other places?
        let c = ir::Constant::int(0, ir::Dtype::INT);
        let inner_dtype = ir::Dtype::pointer(*inner.clone());
        let inst = Instruction::GetElementPtr {
            ptr: op,
            offset: ir::Operand::constant(c),
            dtype: inner_dtype,
        };
        context.insert_instruction(inst).unwrap()
    } else {
        load_direct(op, should_load, context)
    }
}

fn type_size(t: &TypeSpecifier) -> Option<usize> {
    let r = match t {
        TypeSpecifier::Char => 1,
        TypeSpecifier::Short => 2,
        TypeSpecifier::Int => 4,
        TypeSpecifier::Long => 8,
        TypeSpecifier::Float => 4,
        TypeSpecifier::Double => 8,
        TypeSpecifier::Bool => 4,
        TypeSpecifier::Atomic(node) => todo!(),
        TypeSpecifier::Struct(node) => todo!(),
        TypeSpecifier::Enum(node) => todo!(),
        TypeSpecifier::TypedefName(node) => todo!(),
        _ => return None,
    };
    Some(r)
}

/// 1. one of them is float
fn basic_type_promotion(l_type: &ir::Dtype, r_type: &ir::Dtype) -> ir::Dtype {
    if l_type == r_type {
        l_type.clone()
    } else if l_type.is_int(None) && r_type.is_int(None) {
        let l_size = l_type.get_int_width().unwrap();
        let r_size = r_type.get_int_width().unwrap();
        if l_size > r_size {
            l_type.clone()
        } else if l_size < r_size {
            r_type.clone()
        } else {
            if l_type.is_int_signed() && !r_type.is_int_signed() {
                r_type.clone()
            } else {
                l_type.clone()
            }
        }
    } else {
        unreachable!("unsupported type promotion, {:?}, {:?}", l_type, r_type)
    }
}

fn type_align(t: &TypeSpecifier) -> Option<usize> {
    let r = match t {
        TypeSpecifier::Char => 1,
        TypeSpecifier::Short => 2,
        TypeSpecifier::Int => 4,
        TypeSpecifier::Long => 8,
        TypeSpecifier::Float => 4,
        TypeSpecifier::Double => 8,
        TypeSpecifier::Bool => 4,
        TypeSpecifier::Atomic(node) => todo!(),
        TypeSpecifier::Struct(node) => todo!(),
        TypeSpecifier::Enum(node) => todo!(),
        TypeSpecifier::TypedefName(node) => todo!(),
        _ => return None,
    };
    Some(r)
}

fn collect_logic_leaf_expr<'a>(
    expr: &'a Expression,
    collects: &mut Vec<&'a Expression>,
    operations: &mut Vec<BinaryOperator>,
) {
    if let Expression::BinaryOperator(node) = &expr
        && (node.node.operator.node == BinaryOperator::LogicalAnd
            || node.node.operator.node == BinaryOperator::LogicalOr)
    {
        collect_logic_leaf_expr(&node.node.lhs.node, collects, operations);
        collect_logic_leaf_expr(&node.node.rhs.node, collects, operations);
        operations.push(node.node.operator.node.clone());
    } else {
        collects.push(expr);
    }
}

#[cfg(test)]
mod tests {

    struct ExprEvaluator;

    impl ExprEvaluator {
        fn eval(&self, expr: &Expression) -> ir::Operand {
            let typedefs = Default::default();
            let structs = Default::default();
            let mut irgen = IrgenFunc {
                return_type: ir::Dtype::unit(),
                bid_init: Irgen::BID_INIT,
                phinodes_init: Vec::new(),
                allocations: Vec::new(),
                blocks: BTreeMap::new(),
                bid_counter: Irgen::BID_COUNTER_INIT,
                tempid_counter: Irgen::TEMPID_COUNTER_INIT,
                typedefs: &typedefs,
                structs: &structs,
                symbol_table: vec![],
            };
            let stmt = Statement::Expression(Some(Box::new(Node {
                node: expr.clone(),
                span: lang_c::span::Span::span(0, 0),
            })));
            let mut context = Context::new(Irgen::BID_INIT);

            irgen.translate_stmt(&stmt, &mut context, None, None);
            todo!()
        }
    }

    use super::*;

    #[test]
    fn test_expr() {}
}
