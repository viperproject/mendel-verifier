#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

mod utils;

/// Source: https://github.com/rust-lang/miri/blob/master/tests/compiletest.rs
use compiletest_rs as compiletest;
use std::{env, path::PathBuf};
use utils::*;

fn run_tests(mode: &str, path: &str, custom_args: Vec<String>) {
    let mut config = compiletest::Config::default();
    let mut flags = Vec::new();
    flags.push("--edition 2018".to_owned());
    flags.push(format!("--sysroot {}", find_sysroot()));
    flags.extend(custom_args.into_iter());
    config.target_rustcflags = Some(flags.join(" "));
    config.mode = mode.parse().expect("Invalid mode");
    config.rustc_path = find_compiled_executable("analysis-driver");
    config.src_base = PathBuf::from(path);
    assert!(config.src_base.is_dir());

    // Filter the tests to run
    if let Some(filter) = env::args().nth(1) {
        config.filters.push(filter);
    }

    if let Some(lib_path) = option_env!("RUSTC_LIB_PATH") {
        config.run_lib_path = PathBuf::from(lib_path);
        config.compile_lib_path = PathBuf::from(lib_path);
    }

    // Update the .stdout so that all tests pass:
    // config.bless = true;

    compiletest::run_tests(&config);
}

fn test_runner(_tests: &[&()]) {
    env::set_var("RUST_BACKTRACE", "1");

    run_tests(
        "ui",
        "tests/test_cases/reaching_definitions",
        vec!["--analysis=ReachingDefsAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/definitely_initialized",
        vec!["--analysis=DefinitelyInitializedAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/relaxed_definitely_initialized",
        vec!["--analysis=RelaxedDefinitelyInitializedAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/maybe_borrowed",
        vec!["--analysis=MaybeBorrowedAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/definitely_blocked",
        vec!["--analysis=DefinitelyUnreachableAnalysis".into()],
    );
    // These tests are disabled because on macOS the compiler generates slightly different MIRs
    // than on Linux and Windows, which causes some tests (`mutex*.rs` and `drop.rs`) to fail.
    if !cfg!(target_os = "macos") {
        run_tests(
            "ui",
            "tests/test_cases/definitely_accessible",
            vec!["--analysis=DefinitelyAccessibleAnalysis".into()],
        );
        run_tests(
            "ui",
            "tests/test_cases/framing",
            vec!["--analysis=FramingAnalysis".into()],
        );
        run_tests(
            "ui",
            "tests/test_cases/locally_shared",
            vec!["--analysis=LocallySharedAnalysis".into()],
        );
    }
}
