mod instructions_template;
mod static_string_indexing;

use instructions_template::generate_instructions_rs;
use static_string_indexing::index_static_strings;

use std::env;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

fn find_prolog_files(
    libraries: &mut File,
    path_prefix: &str,
    const_prefix: &str,
    current_dir: &Path,
) -> Vec<(String, String)> {
    let mut constants = vec![];

    let entries = match current_dir.read_dir() {
        Ok(entries) => entries,
        Err(_) => return constants,
    };

    for entry in entries.filter_map(Result::ok).map(|e| e.path()) {
        if entry.is_dir() {
            if let Some(file_name) = entry.file_name() {
                let file_name = file_name.to_str().unwrap();
                let new_path_prefix = format!("{path_prefix}{file_name}/");
                let new_const_prefix = format!("{const_prefix}_{}", file_name.to_uppercase());
                let new_consts =
                    find_prolog_files(libraries, &new_path_prefix, &new_const_prefix, &entry);
                constants.extend(new_consts);
            }
        } else if entry.is_file() {
            let ext = std::ffi::OsStr::new("pl");
            if entry.extension() == Some(ext) {
                let contain = String::from_utf8(fs::read(&entry).unwrap()).unwrap();
                let name = entry.file_stem().unwrap().to_str().unwrap();
                let lib_name = format!("{path_prefix}{name}");
                let const_name = format!("{const_prefix}_{}", name.to_uppercase());

                writeln!(libraries, "const {const_name}: &str = {contain:?};").unwrap();

                constants.push((lib_name, const_name));
            }
        }
    }

    constants
}

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
    let dest_path = Path::new(&out_dir).join("libraries.rs");

    let mut libraries = File::create(dest_path).unwrap();
    let lib_path = Path::new("src/lib");

    writeln!(
        libraries,
        "\
use indexmap::IndexMap;\
    "
    )
    .unwrap();

    let constants = find_prolog_files(&mut libraries, "", "LIB", lib_path);

    writeln!(
        libraries,
        "\
ref_thread_local::ref_thread_local! {{
    pub(crate) static managed LIBRARIES: IndexMap<&'static str, &'static str> = {{
        let mut m = IndexMap::new();"
    )
    .unwrap();

    for (name, constant) in constants {
        writeln!(
            libraries,
            "\
        m.insert(\"{name}\",{constant});"
        )
        .unwrap();
    }

    writeln!(
        libraries,
        "
        m
    }};
}}"
    )
    .unwrap();

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
