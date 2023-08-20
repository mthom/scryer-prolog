use proc_macro2::TokenStream;
use syn::*;
use syn::parse::*;
use syn::visit::*;

use indexmap::IndexSet;

struct StaticStrVisitor {
    static_strs: IndexSet<String>,
}

impl StaticStrVisitor {
    fn new() -> Self {
        Self { static_strs: IndexSet::new() }
    }
}

struct MacroFnArgs {
    args: Vec<Expr>,
}

struct ReadHeapCellExprAndArms {
    expr: Expr,
    arms: Vec<Arm>,
}

impl Parse for ReadHeapCellExprAndArms {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut arms = vec![];
        let expr = input.parse()?;

        input.parse::<Token![,]>()?;
        arms.push(input.parse()?);

        while !input.is_empty() {
            if let Ok(_) = input.parse::<Token![,]>() {}
            arms.push(input.parse()?);
        }

        Ok(ReadHeapCellExprAndArms { expr, arms })
    }
}

impl Parse for MacroFnArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut args = vec![];

        if !input.is_empty() {
            args.push(input.parse()?);
        }

        while !input.is_empty() {
            if let Ok(_) = input.parse::<Token![,]>() {}
            args.push(input.parse()?);
        }

        Ok(MacroFnArgs { args })
    }
}

impl<'ast> Visit<'ast> for StaticStrVisitor {
    fn visit_macro(&mut self, m: &'ast Macro) {
        let Macro { path, .. } = m;

        if path.is_ident("atom") {
            if let Some(Lit::Str(string)) = m.parse_body::<Lit>().ok() {
                self.static_strs.insert(string.value());
            }
        } else if path.is_ident("read_heap_cell") || path.is_ident("match_untyped_arena_ptr") {
            if let Some(m) = m.parse_body::<ReadHeapCellExprAndArms>().ok() {
                self.visit_expr(&m.expr);

                for e in m.arms {
                    self.visit_arm(&e);
                }
            }
        } else {
            if let Some(m) = m.parse_body::<MacroFnArgs>().ok() {
                for e in m.args {
                    self.visit_expr(&e);
                }
            }
        }
    }
}

pub fn index_static_strings(instruction_rs_path: &std::path::Path) -> TokenStream {
    use quote::*;

    use std::ffi::OsStr;
    use std::fs::File;
    use std::io::Read;

    use walkdir::WalkDir;

    fn filter_rust_files(e: &walkdir::DirEntry) -> bool {
        if e.path().is_dir() {
            return true;
        }

        e.path().extension().and_then(OsStr::to_str) == Some("rs")
    }

    let mut visitor = StaticStrVisitor::new();

    fn process_filepath(path: &std::path::Path) -> std::result::Result<syn::File, ()> {
        let mut src = String::new();

        let mut file = match File::open(path) {
            Ok(file) => file,
            Err(_) => return Err(()),
        };

        match file.read_to_string(&mut src) {
            Ok(_) => {}
            Err(e) => {
                panic!("error reading file: {:?}", e);
            }
        }

        let syntax = match syn::parse_file(&src) {
            Ok(s) => s,
            Err(e) => {
                panic!("parse error: {} in file {:?}", e, path);
            }
        };
        Ok(syntax)
    }

    for entry in WalkDir::new("src/")
        .into_iter()
        .filter_entry(filter_rust_files)
    {
        let entry = entry.unwrap();

        if entry.path().is_dir() {
            continue;
        }

        let syntax = match process_filepath(entry.path()) {
            Ok(syntax) => syntax,
            Err(_) => continue,
        };

        visitor.visit_file(&syntax);
    }

    match process_filepath(instruction_rs_path) {
        Ok(syntax) => visitor.visit_file(&syntax),
        Err(_) => {}
    }

    let indices = (0..visitor.static_strs.len()).map(|i| (i << 3) as u64);
    let indices_iter = indices.clone();

    let static_strs_len = visitor.static_strs.len();
    let static_strs: &Vec<_> = &visitor.static_strs.into_iter().collect();

    quote! {
        use phf;

        static STRINGS: [&'static str; #static_strs_len] = [
            #(
                #static_strs,
            )*
        ];

        #[macro_export]
        macro_rules! atom {
            #((#static_strs) => { Atom { index: #indices_iter } };)*
        }

        pub static STATIC_ATOMS_MAP: phf::Map<&'static str, Atom> = phf::phf_map! {
            #(#static_strs => { Atom { index: #indices } },)*
        };
    }
}
