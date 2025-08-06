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
        fs::{File, read_dir},
        io::{self, Write, stderr, stdout},
        path::Path,
    };

    use itertools::Itertools;
    use serde_json::json;
    use tempfile::tempdir;

    use crate::{IrParse, Irgen, IsEquiv, Parse, Translate, ir, write_base::WriteLine};

    const C_DIR: &str = "examples/c/";
    const IR_DIR: &str = "examples/ir0/";

    #[test]
    fn test_dir() -> io::Result<()> {
        let files = read_dir(C_DIR).unwrap();
        let mut names = vec![];
        for file in files {
            let file = file.unwrap();
            let name = file.file_name().into_string().unwrap();
            if name.ends_with(".c") {
                let name = name.strip_suffix(".c").unwrap();
                names.push(name.to_string());
            }
        }
        names.sort();
        let _ = names.remove(names.iter().find_position(|&s| s == "array").unwrap().0);
        let _ = names.remove(
            names
                .iter()
                .find_position(|&s| s == "complete_cond")
                .unwrap()
                .0,
        );
        let _ = names.remove(names.iter().find_position(|&s| s == "float").unwrap().0);
        let _ = names.remove(names.iter().find_position(|&s| s == "fibonacci").unwrap().0);
        let _ = names.remove(names.iter().find_position(|&s| s == "fib2").unwrap().0);
        let _ = names.remove(names.iter().find_position(|&s| s == "fib3").unwrap().0);
        let _ = names.remove(names.iter().find_position(|&s| s == "fib4").unwrap().0);
        let _ = names.remove(names.iter().find_position(|&s| s == "fib5").unwrap().0);
        let _ = names.remove(
            names
                .iter()
                .find_position(|&s| s == "cond_and_loop")
                .unwrap()
                .0,
        );
        let _ = names.remove(names.iter().find_position(|&s| s == "cond").unwrap().0);

        for name in names {
            let res = std::thread::spawn(move || {
                test_writeir(&name).unwrap();
            });
            res.join();
        }
        Ok(())
    }

    #[test]
    fn test_once() -> io::Result<()> {
        test_writeir("float2")?;
        Ok(())
    }

    #[test]
    fn test_all() -> io::Result<()> {
        // test_writeir("complete_cond");
        // test_writeir("logical_op");
        // test_writeir("float2");

        test_writeir("alignof");
        test_writeir("array");
        test_writeir("array2");
        test_writeir("array3");
        test_writeir("array4");
        test_writeir("array5");
        test_writeir("bar");
        test_writeir("bitwise");
        test_writeir("cmp");
        test_writeir("comma");
        test_writeir("complement");
        test_writeir("cond");
        test_writeir("cond_and_loop");
        test_writeir("fib2");
        test_writeir("fib3");
        test_writeir("fib4");
        test_writeir("fib5");
        test_writeir("fibonacci");
        test_writeir("float");
        test_writeir("foo");
        test_writeir("foo2");
        test_writeir("foo3");
        test_writeir("foo4");
        test_writeir("for_continue_break");
        test_writeir("gcd");
        test_writeir("hello_main");
        test_writeir("integer_literal");
        test_writeir("integer_literal2");
        test_writeir("lost_copy");
        test_writeir("minus_constant");
        test_writeir("negate");
        test_writeir("pointer");
        test_writeir("return_void");
        test_writeir("shift");
        test_writeir("simple");
        test_writeir("simple_cond");
        test_writeir("simple_for");
        test_writeir("simple_if");
        test_writeir("sizeof");
        test_writeir("sizeof2");
        test_writeir("sizeof3");
        test_writeir("sizeof4");
        test_writeir("struct");
        test_writeir("struct2");
        test_writeir("struct3");
        test_writeir("struct4");
        test_writeir("switch");
        test_writeir("switch-in-loop");
        test_writeir("temp");
        test_writeir("temp2");
        test_writeir("test");
        test_writeir("typedef");
        test_writeir("typecast");
        test_writeir("unary");
        test_writeir("while_continue_break");

        Ok(())
    }

    fn test_writeir(file: &str) -> io::Result<()> {
        let mut stdout = stdout();
        let c_path = format!("{C_DIR}{file}.c");
        let ir_path = format!("{IR_DIR}{file}.ir");
        let c_file = Path::new(&c_path);
        let ir_file = Path::new(&ir_path);

        let parse = Parse {}.translate(&c_file).expect("parse failed");
        // println!("{}", json!(parse));

        let ir = Irgen::default().translate(&parse).expect("irgen failed");
        writeln!(stdout, "ir gen of {} by us:", file);
        ir.write_line(0, &mut stdout)?;
        stdout.flush()?;

        let res = ir::interp(&ir, vec![]);
        println!("res: {:?}", res);

        let unit = IrParse {}
            .translate(&ir_file)
            .unwrap_or_else(|_| panic!("parse failed {}", ir_file.display()));

        // assert!(unit.is_equiv(&ir));

        // writeln!(stdout, "\nir gen by ir parse:");
        // // writeln!(stdout, "{:?}", unit);
        // unit.write_line(0, &mut stdout)?;

        Ok(())
    }
}
