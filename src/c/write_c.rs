use std::io::{Result, Write};

use lang_c::ast::*;
use lang_c::span::Node;

use crate::write_base::*;

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
    }
}

impl<T: WriteString> WriteString for Node<T> {
    fn write_string(&self) -> String {
        self.node.write_string()
    }
}

impl WriteLine for TranslationUnit {
    /// VERY BIG HINT: You should start by understanding the [`writeln!`](https://doc.rust-lang.org/std/macro.writeln.html) macro.
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        for node in &self.0 {
            node.write_line(indent, write)?;
        }
        Ok(())
    }
}

impl WriteString for Initializer {
    fn write_string(&self) -> String {
        match self {
            Initializer::Expression(node) => node.write_string(),
            Initializer::List(vec) => {
                let items = vec
                    .iter()
                    .map(|item| item.write_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{}}}", items)
            }
        }
    }
}

impl WriteString for InitializerListItem {
    fn write_string(&self) -> String {
        let designation = self
            .designation
            .iter()
            .map(|d| d.write_string())
            .collect::<Vec<_>>()
            .join("");
        if designation.is_empty() {
            self.initializer.write_string()
        } else {
            format!("{} = {}", designation, self.initializer.write_string())
        }
    }
}

impl WriteString for Designator {
    fn write_string(&self) -> String {
        match self {
            Designator::Index(node) => format!("[{}]", node.write_string()),
            Designator::Member(node) => format!(".{}", node.write_string()),
            Designator::Range(node) => format!(
                "[{} ... {}]",
                node.node.from.write_string(),
                node.node.to.write_string()
            ),
        }
    }
}

impl WriteLine for ExternalDeclaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(write, "{}", "  ".repeat(indent))?;
        match self {
            ExternalDeclaration::FunctionDefinition(func_def) => func_def.write_line(indent, write),
            ExternalDeclaration::Declaration(decl) => decl.write_line(indent, write),
            ExternalDeclaration::StaticAssert(assert) => assert.write_line(indent, write),
        }
    }
}

impl WriteLine for FunctionDefinition {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        let specifiers = self
            .specifiers
            .iter()
            .map(|s| s.write_string())
            .collect::<Vec<_>>()
            .join(" ");
        let declarator = self.declarator.write_string();
        writeln!(write, "{} {}", specifiers, declarator)?;
        self.statement.write_line(1, write)
    }
}

impl WriteString for DeclarationSpecifier {
    fn write_string(&self) -> String {
        match self {
            DeclarationSpecifier::TypeSpecifier(node) => node.write_string(),
            DeclarationSpecifier::StorageClass(node) => node.write_string(),
            DeclarationSpecifier::TypeQualifier(node) => node.write_string(),
            DeclarationSpecifier::Function(node) => todo!(),
            DeclarationSpecifier::Alignment(node) => todo!(),
            DeclarationSpecifier::Extension(vec) => todo!(),
        }
    }
}

impl WriteString for TypeSpecifier {
    fn write_string(&self) -> String {
        match self {
            TypeSpecifier::Void => "void".to_string(),
            TypeSpecifier::Char => "char".to_string(),
            TypeSpecifier::Short => "short".to_string(),
            TypeSpecifier::Int => "int".to_string(),
            TypeSpecifier::Long => "long".to_string(),
            TypeSpecifier::Float => "float".to_string(),
            TypeSpecifier::Double => "double".to_string(),
            TypeSpecifier::Signed => "signed".to_string(),
            TypeSpecifier::Unsigned => "unsigned".to_string(),
            TypeSpecifier::Bool => "_Bool".to_string(),
            TypeSpecifier::Complex => "_Complex".to_string(),
            TypeSpecifier::Atomic(node) => format!("_Atomic({})", node.write_string()),
            TypeSpecifier::Struct(node) => node.write_string(),
            TypeSpecifier::Enum(node) => node.write_string(),
            TypeSpecifier::TypedefName(node) => node.write_string(),
            TypeSpecifier::TypeOf(node) => format!("typeof({})", node.write_string()),
            TypeSpecifier::TS18661Float(ts18661_float_type) => ts18661_float_type.write_string(),
        }
    }
}

impl WriteString for StorageClassSpecifier {
    fn write_string(&self) -> String {
        match self {
            StorageClassSpecifier::Auto => "auto".to_string(),
            StorageClassSpecifier::Register => "register".to_string(),
            StorageClassSpecifier::Static => "static".to_string(),
            StorageClassSpecifier::ThreadLocal => "_Thread_local".to_string(),
            StorageClassSpecifier::Extern => "extern".to_string(),
            StorageClassSpecifier::Typedef => "typedef".to_string(),
        }
    }
}

impl WriteString for TypeQualifier {
    fn write_string(&self) -> String {
        match self {
            TypeQualifier::Const => "const".to_string(),
            TypeQualifier::Volatile => "volatile".to_string(),
            TypeQualifier::Restrict => "restrict".to_string(),
            TypeQualifier::Atomic => "_Atomic".to_string(),
            TypeQualifier::Nonnull => "_Nonnull".to_string(),
            TypeQualifier::NullUnspecified => "_Null_unspecified".to_string(),
            TypeQualifier::Nullable => "_Nullable".to_string(),
        }
    }
}

impl WriteString for FunctionSpecifier {
    fn write_string(&self) -> String {
        match self {
            FunctionSpecifier::Inline => "inline".to_string(),
            FunctionSpecifier::Noreturn => "_Noreturn".to_string(),
        }
    }
}

impl WriteString for AlignmentSpecifier {
    fn write_string(&self) -> String {
        match self {
            AlignmentSpecifier::Type(node) => format!("_Alignas({})", node.write_string()),
            AlignmentSpecifier::Constant(node) => format!("_Alignas({})", node.write_string()),
        }
    }
}

impl WriteString for Extension {
    fn write_string(&self) -> String {
        match self {
            Extension::Attribute(node) => node.write_string(),
            Extension::AsmLabel(node) => format!("__asm__({})", node.write_string()),
            Extension::AvailabilityAttribute(node) => {
                format!("__attribute__((availability({})))", node.write_string())
            }
        }
    }
}

impl WriteString for Attribute {
    fn write_string(&self) -> String {
        if self.arguments.is_empty() {
            format!("__attribute__(({}))", self.name.node)
        } else {
            let args = self
                .arguments
                .iter()
                .map(|arg| arg.write_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("__attribute__(({}({})))", self.name.node, args)
        }
    }
}

impl WriteString for AvailabilityAttribute {
    fn write_string(&self) -> String {
        let clauses = self
            .clauses
            .iter()
            .map(|c| c.write_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "__attribute__((availability({}, {})))",
            self.platform.write_string(),
            clauses
        )
    }
}

impl WriteString for AvailabilityClause {
    fn write_string(&self) -> String {
        match self {
            AvailabilityClause::Introduced(node) => format!("introduced({})", node.write_string()),
            AvailabilityClause::Deprecated(node) => format!("deprecated({})", node.write_string()),
            AvailabilityClause::Obsoleted(node) => format!("obsoleted({})", node.write_string()),
            AvailabilityClause::Unavailable => "unavailable".to_string(),
            AvailabilityClause::Message(node) => format!("message({})", node.write_string()),
            AvailabilityClause::Replacement(node) => {
                format!("replacement({})", node.write_string())
            }
        }
    }
}

impl WriteString for AvailabilityVersion {
    fn write_string(&self) -> String {
        let major = self.major.clone();
        if let Some(minor) = &self.minor {
            if let Some(patch) = &self.subminor {
                format!("{}.{}.{}", major, minor, patch)
            } else {
                format!("{}.{}", major, minor)
            }
        } else {
            major
        }
    }
}

impl WriteString for StructType {
    fn write_string(&self) -> String {
        let t = match &self.kind.node {
            StructKind::Struct => "struct",
            StructKind::Union => "union",
        };
        let firstline = format!("{} {}", t, self.identifier.write_string());
        let fields = match &self.declarations {
            Some(declarations) => declarations
                .iter()
                .map(|d| format!("{};\n", d.write_string()))
                .collect::<Vec<_>>()
                .join(""),
            None => "".to_string(),
        };
        if fields.is_empty() {
            firstline
        } else {
            firstline + " {\n" + &fields + "}"
        }
    }
}

impl WriteString for StructDeclaration {
    fn write_string(&self) -> String {
        match self {
            StructDeclaration::Field(node) => {
                let specifiers = node
                    .node
                    .specifiers
                    .iter()
                    .map(|s| s.write_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                let declarators = node
                    .node
                    .declarators
                    .iter()
                    .map(|d| d.write_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{} {}", specifiers, declarators)
            }
            StructDeclaration::StaticAssert(node) => todo!(),
        }
    }
}

impl WriteString for StructDeclarator {
    fn write_string(&self) -> String {
        let declarator = self
            .declarator
            .as_ref()
            .map(|d| d.write_string())
            .unwrap_or_default();
        let bit_width = self
            .bit_width
            .as_ref()
            .map(|b| format!(": {}", b.write_string()))
            .unwrap_or_default();
        format!("{}{}", declarator, bit_width)
    }
}

impl WriteString for EnumType {
    fn write_string(&self) -> String {
        todo!()
    }
}

impl WriteString for TypeOf {
    fn write_string(&self) -> String {
        match self {
            TypeOf::Expression(node) => node.write_string(),
            TypeOf::Type(node) => node.write_string(),
        }
    }
}

impl WriteString for Declarator {
    fn write_string(&self) -> String {
        let mut result = self.kind.write_string();
        for d in self.derived.iter() {
            match &d.node {
                DerivedDeclarator::Pointer(vec) => {
                    let qualifier = vec
                        .iter()
                        .map(|p| p.write_string())
                        .collect::<Vec<_>>()
                        .join(" ");
                    result = format!("*{}{}", qualifier, result);
                }
                DerivedDeclarator::Array(node) => {
                    result.push_str(&node.write_string());
                }
                DerivedDeclarator::Function(node) => {
                    result.push_str(&format!("({})", node.write_string()));
                }
                DerivedDeclarator::KRFunction(vec) => {
                    result = format!(
                        "{} ({})",
                        result,
                        vec.iter()
                            .map(|p| p.write_string())
                            .collect::<Vec<_>>()
                            .join(" ")
                    );
                }
                DerivedDeclarator::Block(vec) => todo!(),
            }
        }

        let exts = self
            .extensions
            .iter()
            .map(|e| e.write_string())
            .collect::<Vec<_>>()
            .join(" ");
        format!("{} {}", result, exts)
    }
}

impl WriteString for DeclaratorKind {
    fn write_string(&self) -> String {
        match self {
            DeclaratorKind::Abstract => "".to_string(),
            DeclaratorKind::Identifier(node) => node.write_string(),
            DeclaratorKind::Declarator(node) => format!("({})", node.write_string()),
        }
    }
}

impl WriteString for DerivedDeclarator {
    fn write_string(&self) -> String {
        match self {
            DerivedDeclarator::Pointer(vec) => format!(
                "* {}",
                vec.iter()
                    .map(|p| p.write_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            DerivedDeclarator::Array(node) => todo!(),
            DerivedDeclarator::Function(node) => todo!(),
            DerivedDeclarator::KRFunction(vec) => todo!(),
            DerivedDeclarator::Block(vec) => todo!(),
        }
    }
}

impl WriteString for PointerQualifier {
    fn write_string(&self) -> String {
        match self {
            PointerQualifier::TypeQualifier(node) => node.write_string(),
            PointerQualifier::Extension(vec) => vec
                .iter()
                .map(|e| e.write_string())
                .collect::<Vec<_>>()
                .join(" "),
        }
    }
}

impl WriteString for ArrayDeclarator {
    fn write_string(&self) -> String {
        let qualifier = self
            .qualifiers
            .iter()
            .map(|q| q.write_string())
            .collect::<Vec<_>>()
            .join(" ");
        format!("{} {}", qualifier, self.size.write_string())
    }
}

impl WriteString for ArraySize {
    fn write_string(&self) -> String {
        match self {
            ArraySize::Unknown => "[]".to_string(),
            ArraySize::VariableUnknown => "[*]".to_string(),
            ArraySize::VariableExpression(node) => format!("[{}]", node.write_string()),
            ArraySize::StaticExpression(node) => format!("[static {}]", node.write_string()),
        }
    }
}

impl WriteString for FunctionDeclarator {
    fn write_string(&self) -> String {
        let params = self
            .parameters
            .iter()
            .map(|p| p.write_string())
            .collect::<Vec<_>>()
            .join(", ");
        let ellipsis = self.ellipsis.write_string();
        if self.parameters.is_empty() {
            ellipsis
        } else {
            let ellipsis = if ellipsis.is_empty() {
                String::new()
            } else {
                format!(", {}", ellipsis)
            };
            format!("{}{}", params, ellipsis)
        }
    }
}

impl WriteString for ParameterDeclaration {
    fn write_string(&self) -> String {
        let specifiers = self
            .specifiers
            .iter()
            .map(|s| s.write_string())
            .collect::<Vec<_>>()
            .join(" ");
        let declarator = self
            .declarator
            .as_ref()
            .map(|d| d.write_string())
            .unwrap_or_default();
        let exts = self
            .extensions
            .iter()
            .map(|e| e.write_string())
            .collect::<Vec<_>>()
            .join(" ");

        if declarator.is_empty() {
            format!("{} {}", specifiers, exts)
        } else {
            format!("{} {} {}", specifiers, declarator, exts)
        }
    }
}

impl WriteString for Ellipsis {
    fn write_string(&self) -> String {
        match self {
            Ellipsis::None => String::new(),
            Ellipsis::Some => "...".to_string(),
        }
    }
}

impl WriteLine for Statement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Statement::Labeled(node) => node.write_line(indent, write),
            Statement::Compound(vec) => {
                writeln!(write, "{{")?;
                for item in vec {
                    item.write_line(indent, write)?;
                }
                writeln!(write, "}}");
                Ok(())
            }
            Statement::Expression(node) => writeln!(write, "{};", node.write_string()),
            Statement::If(node) => node.write_line(indent, write),
            Statement::Switch(node) => node.write_line(indent, write),
            Statement::While(node) => node.write_line(indent, write),
            Statement::DoWhile(node) => node.write_line(indent, write),
            Statement::For(node) => node.write_line(indent, write),
            Statement::Goto(node) => writeln!(write, "goto {};", node.write_string()),
            Statement::Continue => writeln!(write, "continue;"),
            Statement::Break => {
                writeln!(write, "break;")
            }
            Statement::Return(node) => {
                writeln!(
                    write,
                    "return {};",
                    node.as_ref().map(|n| n.write_string()).unwrap_or_default()
                )
            }
            Statement::Asm(node) => todo!(),
        }
    }
}

impl WriteLine for LabeledStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        writeln!(write, "{}: ", self.label.write_string())?;
        self.statement.write_line(indent, write)
    }
}

impl WriteString for Label {
    fn write_string(&self) -> String {
        match self {
            Label::Identifier(node) => node.write_string(),
            Label::Case(node) => format!("case {}", node.write_string()),
            Label::CaseRange(node) => format!(
                "case {} ... {}",
                node.node.low.write_string(),
                node.node.high.write_string()
            ),
            Label::Default => "default".to_string(),
        }
    }
}

impl WriteLine for BlockItem {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            BlockItem::Declaration(node) => node.write_line(indent, write),
            BlockItem::StaticAssert(node) => node.write_line(indent, write),
            BlockItem::Statement(node) => node.write_line(indent, write),
        }
    }
}

impl WriteLine for IfStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        writeln!(write, "if ({})", self.condition.write_string())?;
        self.then_statement.write_line(indent + 1, write)?;
        if let Some(else_statement) = &self.else_statement {
            writeln!(write, "else")?;
            else_statement.write_line(indent + 1, write)?;
        }
        Ok(())
    }
}

impl WriteLine for ForStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        let parts = [
            self.initializer.write_string(),
            self.condition
                .as_ref()
                .map(|c| c.write_string())
                .unwrap_or_default(),
            self.step
                .as_ref()
                .map(|s| s.write_string())
                .unwrap_or_default(),
        ];
        writeln!(write, "for ({})", parts.join("; "))?;
        self.statement.write_line(indent, write)
    }
}

impl WriteString for ForInitializer {
    fn write_string(&self) -> String {
        match self {
            ForInitializer::Empty => "".to_string(),
            ForInitializer::Expression(node) => node.write_string(),
            ForInitializer::Declaration(node) => node.write_string(),
            ForInitializer::StaticAssert(node) => self.write_string(),
        }
    }
}

impl WriteLine for WhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        writeln!(write, "while ({})", self.expression.write_string())?;
        self.statement.write_line(indent + 1, write)
    }
}

impl WriteLine for DoWhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        writeln!(write, "do")?;
        self.statement.write_line(indent + 1, write)?;
        writeln!(write, "while ({});", self.expression.write_string())
    }
}

impl WriteLine for SwitchStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        writeln!(write, "switch ({})", self.expression.write_string())?;
        self.statement.write_line(indent + 1, write)
    }
}

impl WriteLine for AsmStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        todo!()
    }
}

impl WriteString for Declaration {
    fn write_string(&self) -> String {
        let specifiers = self
            .specifiers
            .iter()
            .map(|s| s.write_string())
            .collect::<Vec<_>>()
            .join(" ");
        let declarators = self
            .declarators
            .iter()
            .map(|d| d.write_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} {}", specifiers, declarators)
    }
}

impl WriteLine for Declaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        writeln!(write, "{};", self.write_string())
    }
}

impl WriteString for InitDeclarator {
    fn write_string(&self) -> String {
        match &self.initializer {
            Some(init) => format!(
                "{} = {}",
                self.declarator.write_string(),
                init.write_string()
            ),
            None => self.declarator.write_string(),
        }
    }
}

impl WriteString for Expression {
    fn write_string(&self) -> String {
        match self {
            Expression::Identifier(node) => node.write_string(),
            Expression::Constant(node) => node.write_string(),
            Expression::StringLiteral(node) => node.write_string(),
            Expression::GenericSelection(node) => node.write_string(),
            Expression::Member(node) => node.write_string(),
            Expression::Call(node) => node.write_string(),
            Expression::CompoundLiteral(node) => node.write_string(),
            Expression::SizeOfTy(node) => node.write_string(),
            Expression::SizeOfVal(node) => node.write_string(),
            Expression::AlignOf(node) => node.write_string(),
            Expression::UnaryOperator(node) => node.write_string(),
            Expression::Cast(node) => node.write_string(),
            Expression::BinaryOperator(node) => format!("({})", node.write_string()),
            Expression::Conditional(node) => node.write_string(),
            Expression::Comma(vec) => {
                let res = vec
                    .iter()
                    .map(|expr| expr.write_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({})", res)
            }
            Expression::OffsetOf(node) => node.write_string(),
            Expression::VaArg(node) => node.write_string(),
            Expression::Statement(node) => todo!(),
        }
    }
}

impl WriteString for Identifier {
    fn write_string(&self) -> String {
        self.name.clone()
    }
}

impl WriteString for Constant {
    fn write_string(&self) -> String {
        match self {
            Constant::Integer(integer) => integer.write_string(),
            Constant::Float(float) => float.write_string(),
            Constant::Character(s) => s.clone(),
        }
    }
}

impl WriteString for Integer {
    fn write_string(&self) -> String {
        let prefix = match self.base {
            IntegerBase::Decimal => "",
            IntegerBase::Hexadecimal => "0x",
            IntegerBase::Octal => "0o",
            IntegerBase::Binary => "0b",
        };
        format!("{}{}{}", prefix, self.number, self.suffix.write_string())
    }
}

impl WriteString for Float {
    fn write_string(&self) -> String {
        let prefix = match self.base {
            FloatBase::Decimal => "",
            FloatBase::Hexadecimal => "0x",
        };
        let format_suffix = self.suffix.format.write_string();
        let imagery_suffix = if self.suffix.imaginary {
            "i"
        } else {
            Default::default()
        };
        format!(
            "{}{}{}{}",
            prefix, self.number, format_suffix, imagery_suffix
        )
    }
}

impl WriteString for FloatFormat {
    fn write_string(&self) -> String {
        match self {
            FloatFormat::Float => "f".to_string(),
            FloatFormat::Double => "".to_string(),
            FloatFormat::LongDouble => "l".to_string(),
            FloatFormat::TS18661Format(inner) => inner.write_string(),
        }
    }
}

impl WriteString for TS18661FloatType {
    fn write_string(&self) -> String {
        let prefix = match self.format {
            TS18661FloatFormat::BinaryInterchange => "f",
            TS18661FloatFormat::BinaryExtended => "f",
            TS18661FloatFormat::DecimalInterchange => "d",
            TS18661FloatFormat::DecimalExtended => "d",
        };

        let suffix = match self.format {
            TS18661FloatFormat::BinaryExtended | TS18661FloatFormat::DecimalExtended => "x",
            _ => "",
        };

        format!("{}{}{}", prefix, self.width, suffix)
    }
}

impl WriteString for IntegerSuffix {
    fn write_string(&self) -> String {
        let r = match (self.size, self.unsigned) {
            (IntegerSize::Int, true) => "U",
            (IntegerSize::Int, false) => "",
            (IntegerSize::Long, true) => "UL",
            (IntegerSize::Long, false) => "L",
            (IntegerSize::LongLong, true) => "ULL",
            (IntegerSize::LongLong, false) => "LL",
        };
        format!(
            "{}{}",
            r,
            if self.imaginary {
                "i"
            } else {
                Default::default()
            }
        )
    }
}

impl WriteString for StringLiteral {
    fn write_string(&self) -> String {
        self.iter()
            .map(|s| format!("\"{}\"", s))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl WriteString for GenericSelection {
    fn write_string(&self) -> String {
        format!(
            "_Generic({}, {})",
            self.expression.write_string(),
            self.associations
                .iter()
                .map(|t| match &t.node {
                    GenericAssociation::Type(node) => format!(
                        "{}: {}",
                        node.node.type_name.write_string(),
                        node.node.expression.write_string()
                    ),
                    GenericAssociation::Default(node) =>
                        format!("default: {}", node.write_string()),
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl WriteString for MemberExpression {
    fn write_string(&self) -> String {
        let op = match self.operator.node {
            MemberOperator::Direct => ".",
            MemberOperator::Indirect => "->",
        };
        format!(
            "{}{}{}",
            self.expression.write_string(),
            op,
            self.identifier.write_string()
        )
    }
}

impl WriteString for CallExpression {
    fn write_string(&self) -> String {
        format!(
            "{}({})",
            self.callee.write_string(),
            self.arguments
                .iter()
                .map(|arg| arg.write_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl WriteString for CompoundLiteral {
    fn write_string(&self) -> String {
        todo!()
    }
}

impl WriteString for SizeOfTy {
    fn write_string(&self) -> String {
        format!("sizeof({})", self.0.write_string())
    }
}

impl WriteString for TypeName {
    fn write_string(&self) -> String {
        let specifiers = self
            .specifiers
            .iter()
            .map(|s| s.write_string())
            .collect::<Vec<_>>()
            .join(" ");
        format!(
            "{} {}",
            specifiers,
            self.declarator
                .as_ref()
                .map_or(String::new(), |d| d.write_string())
        )
    }
}

impl WriteString for SpecifierQualifier {
    fn write_string(&self) -> String {
        match self {
            SpecifierQualifier::TypeSpecifier(node) => node.write_string(),
            SpecifierQualifier::TypeQualifier(node) => node.write_string(),
            SpecifierQualifier::Extension(vec) => vec
                .iter()
                .map(|e| e.write_string())
                .collect::<Vec<_>>()
                .join(" "),
        }
    }
}

impl WriteString for SizeOfVal {
    fn write_string(&self) -> String {
        format!("sizeof({})", self.0.write_string())
    }
}

impl WriteString for AlignOf {
    fn write_string(&self) -> String {
        format!("_Alignof({})", self.0.write_string())
    }
}

impl WriteString for UnaryOperatorExpression {
    fn write_string(&self) -> String {
        match self.operator.node {
            UnaryOperator::Plus => format!("(+{})", self.operand.write_string()),
            UnaryOperator::Minus => format!("(-{})", self.operand.write_string()),
            UnaryOperator::PostIncrement => format!("({}++)", self.operand.write_string()),
            UnaryOperator::PostDecrement => format!("({}--)", self.operand.write_string()),
            UnaryOperator::PreIncrement => format!("(++{})", self.operand.write_string()),
            UnaryOperator::PreDecrement => format!("(--{})", self.operand.write_string()),
            UnaryOperator::Address => format!("(&({}))", self.operand.write_string()),
            UnaryOperator::Indirection => format!("(*({}))", self.operand.write_string()),
            UnaryOperator::Complement => format!("(~({}))", self.operand.write_string()),
            UnaryOperator::Negate => format!("(!({}))", self.operand.write_string()),
        }
    }
}

impl WriteString for CastExpression {
    fn write_string(&self) -> String {
        format!(
            "({}) ({})",
            self.type_name.write_string(),
            self.expression.write_string()
        )
    }
}

impl WriteString for BinaryOperatorExpression {
    fn write_string(&self) -> String {
        if matches!(self.operator.node, BinaryOperator::Index) {
            format!("{}[{}]", self.lhs.write_string(), self.rhs.write_string())
        } else {
            format!(
                "{} {} {}",
                self.lhs.write_string(),
                self.operator.node.write_string(),
                self.rhs.write_string()
            )
        }
    }
}

impl WriteString for BinaryOperator {
    fn write_string(&self) -> String {
        match self {
            BinaryOperator::Multiply => "*".to_string(),
            BinaryOperator::Divide => "/".to_string(),
            BinaryOperator::Modulo => "%".to_string(),
            BinaryOperator::ShiftLeft => "<<".to_string(),
            BinaryOperator::ShiftRight => ">>".to_string(),
            BinaryOperator::BitwiseAnd => "&".to_string(),
            BinaryOperator::BitwiseXor => "^".to_string(),
            BinaryOperator::BitwiseOr => "|".to_string(),
            BinaryOperator::LogicalAnd => "&&".to_string(),
            BinaryOperator::LogicalOr => "||".to_string(),
            BinaryOperator::Index => unreachable!(),
            BinaryOperator::Plus => "+".to_string(),
            BinaryOperator::Minus => "-".to_string(),
            BinaryOperator::Less => "<".to_string(),
            BinaryOperator::Greater => ">".to_string(),
            BinaryOperator::LessOrEqual => "<=".to_string(),
            BinaryOperator::GreaterOrEqual => ">=".to_string(),
            BinaryOperator::Equals => "==".to_string(),
            BinaryOperator::NotEquals => "!=".to_string(),
            BinaryOperator::Assign => "=".to_string(),
            BinaryOperator::AssignMultiply => "*=".to_string(),
            BinaryOperator::AssignDivide => "/=".to_string(),
            BinaryOperator::AssignModulo => "%=".to_string(),
            BinaryOperator::AssignPlus => "+=".to_string(),
            BinaryOperator::AssignMinus => "-=".to_string(),
            BinaryOperator::AssignShiftLeft => "<<=".to_string(),
            BinaryOperator::AssignShiftRight => ">>=".to_string(),
            BinaryOperator::AssignBitwiseAnd => "&=".to_string(),
            BinaryOperator::AssignBitwiseXor => "^=".to_string(),
            BinaryOperator::AssignBitwiseOr => "|=".to_string(),
        }
    }
}

impl WriteString for ConditionalExpression {
    fn write_string(&self) -> String {
        format!(
            "({} ? {} : {})",
            self.condition.write_string(),
            self.then_expression.write_string(),
            self.else_expression.write_string()
        )
    }
}

impl WriteString for OffsetOfExpression {
    fn write_string(&self) -> String {
        todo!()
    }
}

impl WriteString for OffsetDesignator {
    fn write_string(&self) -> String {
        todo!()
    }
}

impl WriteString for VaArgExpression {
    fn write_string(&self) -> String {
        todo!()
    }
}

impl WriteLine for StaticAssert {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        todo!()
    }
}
#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Write;

    use serde_json::json;
    use tempfile::tempdir;

    use crate::{IsEquiv, Parse, Translate, write_base::WriteLine};

    const TESTED: &str = r#"
static const int*x=1;
extern int printf(const char*,...);
int main() {
    int a,b,c;
    if (a) {
       b++;
    }
    while (b) {
       b--;
    }
    label1: {
       c-=1;
    }

    do {
        c+=1;
    } while (c < 10);
    return 1;
}
int foo(int x, int yyyy, int z, ...) {
    int a = 1;
    if (x == y) {
        return y;
    } else {
        return z;
    }
}

void init(int row, int col, int a[4][5]) {
    for (int i = 0; i < row; i++) {
        for (int j = 0; j < col; j++) {
            a[i][j] = i * j;
        }
    }
}

int test_switch() {
    int a = 1;
    int b = 0;
    switch (a) {
        case 0: {
            b += 1;
            break;
        }
        case 1: {
            b += 2;
            break;
        }
        default: {
            b += 3;
            break;
        }
    }

    return b == 2;
}
struct Sub {
    long m1;
    long m2;
    long m3;
    long m4;
};

struct Big {
    struct Sub m1;
    struct Sub m2;
    struct Sub m3;
};
"#;
    #[test]
    fn t1() {
        let input = r#"
int foo(int x, int y, int z) {
    if (x == y) {
        return y;
    } else {
        return z;
    }
}

int main() {
    return foo(0, 1, -1) == -1;
}

        "#;

        let temp_dir = tempdir().expect("temp dir creation failed");
        let temp_file_path = temp_dir.path().join("temp.c");
        let mut temp_file = File::create(&temp_file_path).unwrap();
        temp_file
            .write_all(input.as_bytes())
            .expect("failed to write to temp file");

        let unit = Parse
            .translate(&temp_file_path)
            .unwrap_or_else(|_| panic!("parse failed {}", temp_file_path.display()));
        // println!("{:?}", unit);
        println!("{}", json!(unit));
        unit.write_line(0, &mut std::io::stdout())
            .expect("failed to write output");

        let temp_verify_file_path = temp_dir.path().join("temp_verify.c");
        let mut temp_verify_file = File::create(&temp_verify_file_path).unwrap();
        unit.write_line(0, &mut temp_verify_file)
            .expect("failed to write to verify file");

        let verify_unit = Parse
            .translate(&temp_verify_file_path)
            .unwrap_or_else(|_| panic!("parse failed {}", temp_verify_file_path.display()));
        assert!(unit.is_equiv(&verify_unit), "{:?}", verify_unit);
    }
}
