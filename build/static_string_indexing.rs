use proc_macro2::TokenStream;
use syn::parse::*;
use syn::visit::*;
use syn::*;

use indexmap::IndexSet;

struct StaticStrVisitor {
    static_strs: IndexSet<String>,
}

impl StaticStrVisitor {
    fn new() -> Self {
        Self {
            static_strs: IndexSet::new(),
        }
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
            let _ = input.parse::<Token![,]>();
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
            let _ = input.parse::<Token![,]>();
            args.push(input.parse()?);
        }

        Ok(MacroFnArgs { args })
    }
}

impl<'ast> Visit<'ast> for StaticStrVisitor {
    fn visit_macro(&mut self, m: &'ast Macro) {
        let Macro { path, .. } = m;

        if path.is_ident("atom") {
            if let Ok(Lit::Str(string)) = m.parse_body::<Lit>() {
                self.static_strs.insert(string.value());
            }
        } else if path.is_ident("read_heap_cell") || path.is_ident("match_untyped_arena_ptr") {
            if let Ok(m) = m.parse_body::<ReadHeapCellExprAndArms>() {
                self.visit_expr(&m.expr);

                for e in m.arms {
                    self.visit_arm(&e);
                }
            }
        } else if let Ok(m) = m.parse_body::<MacroFnArgs>() {
            for e in m.args {
                self.visit_expr(&e);
            }
        }
    }
}

const INLINED_ATOM_MAX_LEN: usize = 6;

fn static_string_index(string: &str, index: usize) -> u64 {
    if !string.is_empty() && string.len() <= INLINED_ATOM_MAX_LEN && !string.contains('\u{0}') {
        let mut string_buf: [u8; 8] = [0u8; 8];
        string_buf[..string.len()].copy_from_slice(string.as_bytes());
        (u64::from_le_bytes(string_buf) << 1) | 1
    } else {
        (index << 1) as u64
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
                panic!("error reading file: {e:?}");
            }
        }

        let syntax = match syn::parse_file(&src) {
            Ok(s) => s,
            Err(e) => {
                println!("cargo::warning=parse error: {e} in file {path:?}");
                syn::File {
                    shebang: None,
                    attrs: vec![],
                    items: vec![],
                }
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

    if let Ok(syntax) = process_filepath(instruction_rs_path) {
        visitor.visit_file(&syntax)
    }

    let mut static_str_keys = vec![];
    let mut static_strs = vec![];
    let mut static_str_indices = vec![];

    let indices: Vec<u64> = visitor
        .static_strs
        .iter()
        .map(|string| {
            let index = static_string_index(string, static_strs.len());

            static_str_keys.push(string);

            if index & 1 == 1 {
                index
            } else {
                static_str_indices.push(index);
                static_strs.push(string);
                index
            }
        })
        .collect();

    let static_strs_len = static_strs.len();

    quote! {
        static STRINGS: [&str; #static_strs_len] = [
            #(
                #static_strs,
            )*
        ];

        macro_rules! atom {
            #((#static_str_keys) => { Atom { index: #indices } };)*
            ($name:literal) => {compile_error!(concat!("unknown static atom ", $name))};
        }

        pub static STATIC_ATOMS_MAP: phf::Map<&'static str, Atom> = phf::phf_map! {
            #(#static_strs => { Atom { index: #static_str_indices } },)*
        };
    }
}
