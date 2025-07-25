use std::io::{Result, Write};

use crate::ir::*;
use crate::write_base::*;

impl WriteLine for TranslationUnit {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        // TODO: consider KECC IR parser in the future.
        let mut structs = self.structs.iter().collect::<Vec<_>>();
        structs.sort_unstable_by_key(|&(name, _)| name);
        for (name, struct_type) in structs {
            let definition = if let Some(struct_type) = struct_type {
                let fields = struct_type
                    .get_struct_fields()
                    .expect("`struct_type` must be struct type")
                    .as_ref()
                    .expect("`fields` must be `Some`");

                let fields = fields.iter().format_with(", ", |field, f| {
                    f(&format_args!(
                        "{}:{}",
                        if let Some(name) = field.name() {
                            name
                        } else {
                            "%anon"
                        },
                        field.deref()
                    ))
                });

                format!("{{ {fields} }}")
            } else {
                "opaque".to_string()
            };

            writeln!(write, "struct {name} : {definition}")?;
        }

        for (name, decl) in &self.decls {
            if decl.get_variable().is_some() {
                (name, decl).write_line(indent, write)?;
            }
        }

        for (name, decl) in &self.decls {
            if decl.get_function().is_some() {
                writeln!(write)?;
                (name, decl).write_line(indent, write)?;
            }
        }

        Ok(())
    }
}

impl WriteLine for (&String, &Declaration) {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        let name = self.0;
        let decl = self.1;

        match decl {
            Declaration::Variable { dtype, initializer } => {
                writeln!(
                    write,
                    "var {} @{} = {}",
                    dtype,
                    name,
                    if let Some(init) = initializer {
                        init.write_string()
                    } else {
                        "default".to_string()
                    }
                )?;
            }
            Declaration::Function {
                signature,
                definition,
            } => {
                let params = signature.params.iter().format(", ");

                if let Some(definition) = definition.as_ref() {
                    // print function definition
                    writeln!(write, "fun {} @{} ({}) {{", signature.ret, name, params)?;
                    // print meta data for function
                    writeln!(
                        write,
                        "init:\n  bid: {}\n  allocations:\n{}",
                        definition.bid_init,
                        definition
                            .allocations
                            .iter()
                            .enumerate()
                            .format_with("\n", |(i, a), f| f(&format_args!(
                                "    %l{}:{}{}",
                                i,
                                a.deref(),
                                if let Some(name) = a.name() {
                                    format!(":{name}")
                                } else {
                                    "".into()
                                }
                            )))
                    )?;

                    for (id, block) in &definition.blocks {
                        writeln!(write, "\nblock {id}:")?;
                        (id, block).write_line(indent + 1, write)?;
                    }

                    writeln!(write, "}}")?;
                } else {
                    // print declaration line only
                    writeln!(write, "fun {} @{} ({})", signature.ret, name, params)?;
                    writeln!(write)?;
                }
            }
        }

        Ok(())
    }
}

impl WriteLine for (&BlockId, &Block) {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        for (i, phi) in self.1.phinodes.iter().enumerate() {
            write_indent(indent, write)?;
            writeln!(
                write,
                "{}:{}{}",
                RegisterId::arg(*self.0, i),
                phi.deref(),
                if let Some(name) = phi.name() {
                    format!(":{name}")
                } else {
                    "".into()
                }
            )?;
        }

        for (i, instr) in self.1.instructions.iter().enumerate() {
            write_indent(indent, write)?;
            writeln!(
                write,
                "{}:{}{} = {}",
                RegisterId::temp(*self.0, i),
                instr.dtype(),
                if let Some(name) = instr.name() {
                    format!(":{name}")
                } else {
                    "".into()
                },
                instr
            )?;
        }

        write_indent(indent, write)?;
        writeln!(write, "{}", self.1.exit)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs::File,
        io::{self, Write, stderr, stdout},
        path::Path,
    };

    use serde_json::json;
    use tempfile::tempdir;

    use crate::{IrParse, Irgen, IsEquiv, Parse, Translate, ir, write_base::WriteLine};

    const C_DIR: &str = "examples/c/";
    const IR_DIR: &str = "examples/ir0/";

    /**
         *
    int foo(int x, int y, int z) {
        if (x == y) {
            return y;
        } else {
            return z;
        }
    }

    --> translate into:

    fun i32 @foo (i32, i32, i32) {
    init:
      bid: b0
      allocations:
        %l0:i32:x
        %l1:i32:y
        %l2:i32:z

    block b0:
      %b0:p0:i32:x
      %b0:p1:i32:y
      %b0:p2:i32:z
      %b0:i0:unit = store %b0:p0:i32 %l0:i32*
      %b0:i1:unit = store %b0:p1:i32 %l1:i32*
      %b0:i2:unit = store %b0:p2:i32 %l2:i32*
      %b0:i3:i32 = load %l0:i32*
      %b0:i4:i32 = load %l1:i32*
      %b0:i5:u1 = cmp eq %b0:i3:i32 %b0:i4:i32
      br %b0:i5:u1, b1(), b2()

    block b1:
      %b1:i0:i32 = load %l1:i32*
      ret %b1:i0:i32

    block b2:
      %b2:i0:i32 = load %l2:i32*
      ret %b2:i0:i32

    block b3:
      ret undef:i32

    block b4:
      j b3()

    block b5:
      j b3()
    }
         *
         */

    #[test]
    fn test_writeir() -> io::Result<()> {
        let mut stdout = stdout();
        let file = "struct";
        let c_path = format!("{C_DIR}{file}.c");
        let ir_path = format!("{IR_DIR}{file}.ir");
        let c_file = Path::new(&c_path);
        let ir_file = Path::new(&ir_path);

        let parse = Parse {}.translate(&c_file).expect("parse failed");
        // println!("{}", json!(parse));

        let ir = Irgen::default().translate(&parse).expect("irgen failed");
        writeln!(stdout, "ir gen by us:");
        ir.write_line(0, &mut stdout)?;
        stdout.flush()?;

        let unit = IrParse {}
            .translate(&ir_file)
            .unwrap_or_else(|_| panic!("parse failed {}", ir_file.display()));
        assert!(unit.is_equiv(&ir));

        // writeln!(stdout, "\nir gen by ir parse:");
        // // writeln!(stdout, "{:?}", unit);
        // unit.write_line(0, &mut stdout)?;

        Ok(())
    }
}
