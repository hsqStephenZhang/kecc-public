// use lang_c::ast;

// use crate::ir::Dtype;

// #[derive(Clone, Debug, Copy)]
// pub struct Int {
//     width: usize,
//     is_signed: bool,
// }

// impl PartialEq for Int {
//     fn eq(&self, other: &Self) -> bool {
//         self.width == other.width
//     }
// }

// // ranking rules:
// // 1. first cmp it's width
// impl PartialOrd for Int {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         self.width.partial_cmp(&other.width)
//     }
// }

// #[derive(Clone, Debug, Copy)]
// pub struct Float {
//     width: usize,
// }

// impl PartialEq for Float {
//     fn eq(&self, other: &Self) -> bool {
//         self.width == other.width
//     }
// }

// impl PartialOrd for Float {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         self.width.partial_cmp(&other.width)
//     }
// }

// #[derive(Debug, Clone, PartialEq)]
// pub enum PureType {
//     Unit,
//     Int(Int),
//     Float(Float),
// }

// impl TryFrom<&Dtype> for PureType {
//     type Error = ();

//     fn try_from(value: &Dtype) -> Result<Self, Self::Error> {
//         let res = match value {
//             Dtype::Unit { .. } => Self::Unit,
//             &Dtype::Int {
//                 width, is_signed, ..
//             } => Self::Int(Int { width, is_signed }),
//             &Dtype::Float { width, .. } => Self::Float(Float { width }),
//             _ => return Err(()),
//         };
//         Ok(res)
//     }
// }

// impl Dtype {
//     pub fn int_protomotion(&self) -> Self {
//         let Self::Int {
//             width,
//             is_signed,
//             is_const,
//         } = self
//         else {
//             unreachable!()
//         };
//         Self::Int {
//             width: 32,
//             is_signed: false,
//             is_const: *is_const,
//         }
//     }

//     pub fn bin_op(&self, other: &Self, op: &ast::BinaryOperator) -> Option<Self> {
//         // self.is_scalar();
//         todo!()
//     }
// }
