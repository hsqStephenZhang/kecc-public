use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use lang_c::ast;

use crate::asm::TranslationUnit;
use crate::ir::HasDtype;
use crate::opt::opt_utils;
use crate::{Translate, asm, ir};

#[derive(Debug, Default)]
pub struct Asmgen {}

impl Translate<ir::TranslationUnit> for Asmgen {
    type Target = asm::Asm;
    type Error = ();

    fn translate(&mut self, source: &ir::TranslationUnit) -> Result<Self::Target, Self::Error> {
        let asm = asm::Asm {
            unit: TranslationUnit {
                functions: vec![],
                variables: vec![],
            },
        };

        Ok(asm)
    }
}
