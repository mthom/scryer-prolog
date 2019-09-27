extern crate indexmap;

use indexmap::IndexSet;

use std::fs::{File, read_dir};
use std::io::Write;
use std::path::Path;

fn main()
{
    let dest_path = Path::new("./src/prolog/machine/libraries.rs");

    let mut libraries = File::create(&dest_path).unwrap();
    let mut library_index = IndexSet::new();

    let paths = read_dir("./src/prolog/lib").unwrap();

    for item in paths {
        let item = item.unwrap().path();

        if item.is_file() {
            if let Some(ext) = item.extension() {
                if ext == "pl" {
                    let file_stem = item.file_stem().unwrap();
                    let file_str  = file_stem.to_string_lossy().to_uppercase();

                    let include_line = format!("static {}: &str = include_str!(\"{}/{}.pl\");\n",
                                               file_str, "../lib", file_stem.to_string_lossy());

                    libraries.write_all(include_line.as_bytes()).unwrap();
                    library_index.insert(file_stem.to_string_lossy().to_string());
                }
            }
        }
    }

    libraries.write_all(b"\nref_thread_local! {
    pub static managed LIBRARIES: IndexMap<&'static str, &'static str> = {
        let mut m = IndexMap::new();\n").unwrap();

    for item in library_index {
        let line = format!("\n        m.insert(\"{}\", {});", item, item.to_uppercase());
        libraries.write_all(line.as_bytes()).unwrap();
    }

    libraries.write_all(b"\n\n        m\n    };
}").unwrap();
}
