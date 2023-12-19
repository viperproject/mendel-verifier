use std::{env, fs::File, io::Write, path::Path};
use vir_gen::generate_vir;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=defs");
    for entry in walkdir::WalkDir::new("defs") {
        let entry = entry.unwrap();
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }

    let out_dir_string = env::var("OUT_DIR").unwrap();
    let out_dir = Path::new(&out_dir_string);
    let gen_dir = out_dir.join("gen");
    generate_vir(Path::new("defs"), &gen_dir);

    // Write a file that imports the generated module by absolute path.
    let import_src = vec![
        // If only it wasn't generated automatically
        // so that one could do `clippy --fix`...
        "#[allow(clippy::uninlined_format_args)]".to_string(),
        "#[rustfmt::skip]".to_string(),
        format!("#[path = \"{}\"]", gen_dir.join("mod.rs").display()),
        "mod gen;".to_string(),
    ]
    .join("\n");
    let mut import_file = File::create(out_dir.join("import_gen.rs")).unwrap_or_else(|e| {
        panic!("{}", e);
    });
    import_file
        .write_all(import_src.as_bytes())
        .unwrap_or_else(|e| {
            panic!("{}", e);
        });
}
