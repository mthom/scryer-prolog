mod instructions_template;
mod static_string_indexing;

use instructions_template::generate_instructions_rs;
use static_string_indexing::index_static_strings;

use std::env;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

fn main() {
    let has_rustfmt = Command::new("rustfmt")
        .arg("--version")
        .stdin(Stdio::inherit())
        .status()
        .is_ok();

    if !has_rustfmt {
        println!("Failed to run rustfmt, will skip formatting generated files.")
    }

    let out_dir = env::var("OUT_DIR").unwrap();

    let instructions_path = Path::new(&out_dir).join("instructions.rs");
    let mut instructions_file = File::create(&instructions_path).unwrap();

    let quoted_output = generate_instructions_rs();

    instructions_file
        .write_all(quoted_output.to_string().as_bytes())
        .unwrap();

    if has_rustfmt {
        format_generated_file(instructions_path.as_path());
    }

    let static_atoms_path = Path::new(&out_dir).join("static_atoms.rs");
    let mut static_atoms_file = File::create(&static_atoms_path).unwrap();

    let quoted_output = index_static_strings(&instructions_path);

    static_atoms_file
        .write_all(quoted_output.to_string().as_bytes())
        .unwrap();

    if has_rustfmt {
        format_generated_file(static_atoms_path.as_path());
    }

    println!("cargo:rerun-if-changed=src/");
}

fn format_generated_file(path: &Path) {
    Command::new("rustfmt")
        .arg(path.as_os_str())
        .spawn()
        .unwrap_or_else(|err| {
            panic!(
                "{}: rustfmt was detected as available, but failed to format generated file '{}'",
                err,
                path.display()
            );
        })
        .wait()
        .unwrap();
}
