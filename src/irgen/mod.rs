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

/// type cast: https://en.cppreference.com/w/c/language/conversion.html
/// we implement the following cast rules:
///     1. Conversion as if by assignment
///     2. Usual arithmetic conversions
///         a. one of operands is float
///         b. ...
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
                    UnaryOperator::Address => {
                        todo!()
                    }
                    UnaryOperator::Indirection => todo!(),
                    _ => op,
                })
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
                let value = self.translate_expr(&node.node, false, context)?;
                // assign cast2: initialization
                let value = cast(value, &dtype, context);
                let inst = Instruction::Store {
                    ptr: ptr.clone(),
                    value: value.clone(),
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
                let op = self.translate_expr(&condition.node, true, context)?;

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
                let op = self.translate_expr(&node.node.expression.node, false, context)?;
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
                let op = self.translate_expr(&node.node.expression.node, false, &mut ctx_cond)?;
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
                let op = self.translate_expr(&node.node.expression.node, false, &mut ctx_cond)?;
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
                    let op = self.translate_expr(&cond.node, true, &mut ctx_cond)?;
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
                    let op = self.translate_expr(&node.node, true, context)?;
                    let op = if op.local_rid().is_some() {
                        let ptr = op.to_pointer().unwrap();
                        let load = Instruction::Load { ptr };
                        context.insert_instruction(load).unwrap()
                    } else {
                        op
                    };
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

    fn get_orig_ptr(&mut self, expr: &Expression) -> Option<ir::Operand> {
        match expr {
            Expression::Identifier(node) => {
                let value = self.find_symbol(&node.node.name).cloned();
                let op = match value {
                    Some(op) => op,
                    None => panic!("{}, symbol table: {:?}", json!(expr), self.symbol_table),
                };
                Some(op)
            }
            _ => None,
        }
    }

    /// translate expr, will walk the expr tree in post order
    /// ```C
    ///    a = b + c * d;
    /// ```
    fn translate_expr(
        &mut self,
        expr: &Expression,
        no_deref: bool,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenError> {
        // TODO: conditional expr
        let op = match expr {
            Expression::Identifier(node) => {
                let value = self.find_symbol(&node.node.name).cloned();
                let op = match value {
                    Some(op) => op,
                    None => panic!("{}, symbol table: {:?}", json!(expr), self.symbol_table),
                };
                // TODO: when shall we load the value from allocation?
                // if it's the first access of the function argument
                // store the value from function arg to local allocation slot

                if !no_deref && (op.is_global() || op.is_alloc() || op.is_arg()) {
                    let load = Instruction::Load { ptr: op };
                    context.insert_instruction(load).unwrap()
                } else {
                    op
                }
            }
            Expression::Constant(node) => {
                let constant = ir::Constant::try_from(&node.node).unwrap();
                ir::Operand::constant(constant)
            }
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
                if let Some((is_pre, bin_op)) = assign_unary_pre_or_post(&node.node.operator.node) {
                    // expr
                    let op = self.translate_expr(&node.node.operand.node, false, context)?;
                    let dtype = op.dtype();
                    let ptr = self.get_orig_ptr(&node.node.operand.node).unwrap();
                    // i1
                    let const1 = ir::Constant::int(1, dtype.clone());
                    let inst1 = Instruction::BinOp {
                        op: bin_op,
                        lhs: op.clone(),
                        rhs: ir::Operand::Constant(const1),
                        dtype: dtype.clone(),
                    };
                    // i2
                    let op1 = context.insert_instruction(inst1).unwrap();
                    // TODO: do we need type cast here?
                    // `a++` is not the same as `a+=1`,
                    // in `a+=1`, 1 is an int
                    // but in `a++`, we create a const 1 with the same type of a
                    let store = Instruction::Store {
                        ptr,
                        value: op1.clone(),
                    };
                    let _ = context.insert_instruction(store);
                    // finalize operand
                    if is_pre { op1 } else { op }
                } else {
                    let operand = self.translate_expr(&node.node.operand.node, false, context)?;
                    let dtype = operand.dtype();
                    let inst = Instruction::UnaryOp {
                        op: node.node.operator.node.clone(),
                        operand,
                        dtype,
                    };
                    context.insert_instruction(inst).unwrap()
                }
            }
            /// TODO: type cast
            /// TODO: logical expression evaluation
            ///
            /// if is assign (can be = or ++), then lhs must be a pointer, rhs must be a value
            /// if not, then lhs and rhs are both values
            Expression::BinaryOperator(node) => {
                // both lhs and rhs might be a local allocation
                // use the `maybe_load_local` instead of `translate_expr` result

                /// if node's operator is +=, -=, *=, then transform into the corresponding
                /// more and insert the following extra instructions:
                /// lhs += rhs:
                ///      %1 = add lhs rhs
                ///      %2 = store %1
                ///
                /// should return %2
                if let Some(assign_op) = assign_binop(&node.node.operator.node) {
                    let lhs = self.translate_expr(&node.node.lhs.node, false, context)?;
                    let rhs = self.translate_expr(&node.node.rhs.node, false, context)?;
                    let lhs_ptr = self.get_orig_ptr(&node.node.lhs.node).unwrap();
                    let dtype_ptr = lhs_ptr.dtype();
                    let dtype = dtype_ptr.get_pointer_inner().cloned().unwrap();
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
                    let store = Instruction::Store {
                        ptr: lhs_ptr,
                        value: op2.clone(),
                    };
                    let _ = context.insert_instruction(store);
                    op2
                } else if matches!(&node.node.operator.node, BinaryOperator::Assign) {
                    let lhs = self.translate_expr(&node.node.lhs.node, true, context)?;
                    let rhs = self.translate_expr(&node.node.rhs.node, false, context)?;
                    let dtype_ptr = lhs.dtype();
                    let dtype = dtype_ptr.get_pointer_inner().cloned().unwrap_or(dtype_ptr);
                    let rhs = cast(rhs, &dtype, context);
                    let store = Instruction::Store {
                        ptr: lhs,
                        value: rhs.clone(),
                    };
                    let _ = context.insert_instruction(store);
                    rhs
                } else if matches!(&node.node.operator.node, BinaryOperator::Index) {
                    let lhs = self.translate_expr(&node.node.lhs.node, false, context)?;
                    let rhs = self.translate_expr(&node.node.rhs.node, false, context)?;
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
                } else {
                    let lhs = self.translate_expr(&node.node.lhs.node, false, context)?;
                    let rhs = self.translate_expr(&node.node.rhs.node, false, context)?;
                    let mut rhs = rhs;
                    let dtype = match lhs.binop_dtype(&rhs, &node.node.operator.node) {
                        Some(dtype) => dtype,
                        None => {
                            let cast = Instruction::TypeCast {
                                value: rhs,
                                target_dtype: lhs.dtype(),
                            };
                            rhs = context.insert_instruction(cast).unwrap();
                            lhs.binop_dtype(&rhs, &node.node.operator.node).unwrap()
                        }
                    };

                    /// x && y && z
                    ///
                    /// b_current:
                    ///     %value_x = eval x
                    ///     %cmp_x = cmp eq %value_x 0 (if value_x is not bit type)
                    ///     %br %cmp_x b_x_nonzero,b_x_zero
                    ///
                    /// b_z...
                    ///     ...
                    ///
                    /// b_y_nonzero:
                    ///     ...
                    ///     jmp b_y_after
                    /// b_y_zero:
                    ///     ...
                    ///     jmp b_y_after
                    /// b_y_after:
                    ///     ...
                    ///
                    /// b_x_nonzero:
                    ///     %value_x = eval x
                    ///     %cmp_x = cmp eq %value_x 0
                    ///     store %cmp_x tmp*
                    ///     jmp b_after_x
                    /// b_x_zero:
                    ///     store %0 tmp*
                    ///     jmp b_after_x
                    /// b_after_x:
                    ///     %is_nonzero = load tmp*
                    ///     br %is_nonzero b_y_nonzero,b_y_zero
                    let inst = Instruction::BinOp {
                        op: node.node.operator.node.clone(),
                        lhs,
                        rhs,
                        dtype,
                    };
                    context.insert_instruction(inst).unwrap()
                }
            }
            Expression::Statement(node) => todo!(),
            Expression::StringLiteral(node) => todo!(),
            Expression::GenericSelection(node) => todo!(),
            Expression::Member(node) => {
                // TODO: make it readable
                let struct_ptr = self.translate_expr(&node.node.expression.node, true, context)?;
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
                flatten_array(op, dtype.get_pointer_inner().unwrap(), context, false)
            }
            Expression::Call(node) => {
                // TODO: if callee is a function pointer
                // callee can be either
                // 1. a global variable of function
                // 2. a function pointer
                let callee = self.translate_expr(&node.node.callee.node, true, context)?;
                let mut dtype = callee.dtype();
                if let Some(inner) = dtype.get_pointer_inner() {
                    dtype = inner.clone()
                };

                if let ir::Dtype::Function { ret, params } = &dtype {
                    let mut args = vec![];
                    assert_eq!(params.len(), node.node.arguments.len());
                    for (expr, target_dtype) in node.node.arguments.iter().zip(params) {
                        let op = self.translate_expr(&expr.node, false, context)?;
                        // assign cast3: function call
                        let op = cast(op, target_dtype, context);
                        args.push(op);
                    }

                    // let callee = self.translate_expr(&node.node.callee.node, false, context)?;
                    let inst = Instruction::Call {
                        callee: callee.clone(),
                        args,
                        return_type: *ret.clone(),
                    };
                    context.insert_instruction(inst).unwrap()
                } else {
                    unreachable!("{callee:?}")
                }
            }
            Expression::CompoundLiteral(node) => todo!(),
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
                ir::Operand::constant(ir::Constant::int(
                    tname[0] as _,
                    ir::Dtype::int(64).signed(false),
                ))
            }
            Expression::SizeOfVal(node) => {
                let dtype = self.type_of_expr(&node.node.0.node).unwrap();
                let (size, _) = dtype.size_align_of(&self.structs).unwrap();
                ir::Operand::constant(ir::Constant::int(
                    size as _,
                    ir::Dtype::int(64).signed(false),
                ))
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
                ir::Operand::constant(ir::Constant::int(tname[0] as _, dtype))
            }
            Expression::Cast(node) => {
                let op = self.translate_expr(&node.node.expression.node, false, context)?;
                // TODO: resolve struct and typedef types
                let dtype = ir::Dtype::try_from(&node.node.type_name.node).unwrap();
                let cast = cast(op, &dtype, context);
                cast
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
                let op = self.translate_expr(&node.node.condition.node, false, context)?;

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
                let op =
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
                let op =
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
                let load = Instruction::Load { ptr: ptr.clone() };
                context.insert_instruction(load).unwrap()
            }
            Expression::Comma(vec) => {
                let mut op = None;
                for expr in vec.iter() {
                    op = Some(self.translate_expr(&expr.node, false, context)?);
                }
                op.unwrap()
            }
            Expression::OffsetOf(node) => todo!(),
            Expression::VaArg(node) => todo!(),
        };

        Ok(op)
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
fn assign_unary_pre_or_post(op: &UnaryOperator) -> Option<(bool, BinaryOperator)> {
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

fn flatten_array(
    op: ir::Operand,
    array_type: &ir::Dtype,
    context: &mut Context,
    should_load: bool,
) -> ir::Operand {
    if let ir::Dtype::Array { inner, .. } = array_type {
        // TODO: why is here i32 rather than i64 in `GetElementPtr` inst in other places?
        let c = ir::Constant::int(0, ir::Dtype::int(32));
        let inner_dtype = ir::Dtype::pointer(*inner.clone());
        let inst = Instruction::GetElementPtr {
            ptr: op,
            offset: ir::Operand::constant(c),
            dtype: inner_dtype,
        };
        context.insert_instruction(inst).unwrap()
    } else if should_load {
        let inst = Instruction::Load { ptr: op };
        context.insert_instruction(inst).unwrap()
    } else {
        op
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
