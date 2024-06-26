// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(custom_test_frameworks)]
// Custom test runner, to avoid libtest being wrapped around compiletest which
// wraps libtest.
#![test_runner(test_runner)]

use compiletest_rs::{common::Mode, run_tests, Config};
use log::{error, info};
use prusti_server::spawn_server_thread;
use std::{env, path::PathBuf};

fn find_prusti_rustc_path() -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        "prusti-rustc.exe"
    } else {
        "prusti-rustc"
    };
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, executable_name]
        .iter()
        .collect();
    if local_prusti_rustc_path.exists() {
        return local_prusti_rustc_path;
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return workspace_prusti_rustc_path;
    }
    panic!(
        "Could not find the {target_directory:?} prusti-rustc binary to be used in tests. \
        It might be that Prusti has not been compiled correctly."
    );
}

/// This type allows to temporary modify an environment variable.
/// When this structure is dropped (falls out of scope), the original value will be restored.
struct TemporaryEnvVar {
    name: String,
    original: Option<String>,
}

impl TemporaryEnvVar {
    /// Temporarily set an environment variable, until the returned value is dropped.
    fn set(name: &str, value: &str) -> Self {
        let original: Option<String> = env::var(name).ok();
        env::set_var(name, value);
        TemporaryEnvVar {
            name: name.to_string(),
            original,
        }
    }
}

impl Drop for TemporaryEnvVar {
    fn drop(&mut self) {
        match self.original {
            Some(ref old_value) => env::set_var(&self.name, old_value),
            None => env::remove_var(&self.name),
        }
    }
}

fn run_prusti_tests(group_name: &str, filter: &Option<String>, rustc_flags: Option<&str>) {
    let mut config = Config {
        rustc_path: find_prusti_rustc_path(),
        ..Config::default()
    };

    // Filter the tests to run
    if let Some(filter) = filter {
        config.filters.push(filter.clone());
    }

    // Add compilation flags
    // mir-opt-level=0 disables MIR optimizations (e.g., const propagation) that might hide bugs.
    config.target_rustcflags = Some(format!(
        "--edition=2018 -Z mir-opt-level=0 {}",
        rustc_flags.unwrap_or("")
    ));

    let path: PathBuf = ["tests", group_name, "ui"].iter().collect();
    if path.exists() {
        config.target_rustcflags = Some(format!(
            "--color=never {}",
            config.target_rustcflags.unwrap_or_default()
        ));
        config.mode = Mode::Ui;
        config.src_base = path;
        run_tests(&config);
    }

    let path: PathBuf = ["tests", group_name, "pass"].iter().collect();
    if path.exists() {
        config.mode = Mode::RunPass;
        config.src_base = path;
        run_tests(&config);
    }

    let path: PathBuf = ["tests", group_name, "fail"].iter().collect();
    if path.exists() {
        config.mode = Mode::CompileFail;
        config.src_base = path;
        run_tests(&config);
    }
}

fn run_no_verification(group_name: &str, filter: &Option<String>) {
    let _temporary_env_vars = (
        TemporaryEnvVar::set("PRUSTI_FULL_COMPILATION", "true"),
        TemporaryEnvVar::set("PRUSTI_NO_VERIFY", "true"),
        TemporaryEnvVar::set("PRUSTI_QUIET", "true"),
    );

    run_prusti_tests(group_name, filter, None);
}

fn run_verification_base(group_name: &str, filter: &Option<String>) {
    let _temporary_env_vars = (
        TemporaryEnvVar::set("PRUSTI_FULL_COMPILATION", "true"),
        TemporaryEnvVar::set("PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT", "true"),
        TemporaryEnvVar::set("PRUSTI_QUIET", "true"),
    );

    run_prusti_tests(group_name, filter, Some("-A warnings"));
}

// fn run_verification_safe_clients_silicon(group_name: &str, filter: &Option<String>) {
//     let _temporary_env_vars = (TemporaryEnvVar::set("PRUSTI_VIPER_BACKEND", "silicon"),);
//     run_verification_base(group_name, filter);
// }

fn run_verification_safe_clients_carbon(group_name: &str, filter: &Option<String>) {
    let _temporary_env_vars = (TemporaryEnvVar::set("PRUSTI_VIPER_BACKEND", "carbon"),);
    run_verification_base(group_name, filter);
}

fn test_runner(_tests: &[&()]) {
    env_logger::init_from_env(env_logger::Env::new().filter_or("PRUSTI_LOG", "warn"));

    // Spawn server process as child (so it stays around until main function terminates)
    let server_address = spawn_server_thread();
    env::set_var("PRUSTI_SERVER_ADDRESS", server_address.to_string());
    let save_verification_cache =
        || match ureq::post(&format!("http://{server_address}/save")).call() {
            Ok(response) => {
                info!("Saving verification cache: {}", response.status_text());
            }
            Err(ureq::Error::Status(_code, response)) => {
                error!("Error while saving verification cache: {response:?}");
            }
            Err(err) => error!("Error while saving verification cache: {err}"),
        };

    // Filter the tests to run
    let filter = env::args().nth(1);

    // Test the parsing of specifications. This doesn't run the verifier.
    println!("[parse]");
    run_no_verification("parse", &filter);

    // Test the type-checking of specifications. This doesn't run the verifier.
    println!("[typecheck]");
    run_no_verification("typecheck", &filter);

    // Test the verifier.
    println!("[verify_safe_clients_carbon]");
    run_verification_safe_clients_carbon("verify_safe_clients", &filter);
    save_verification_cache();

    // Test the verifier.
    // TODO: Disabled until Silicon can report multiple verification errors.
    // println!("[verify_safe_clients_silicon]");
    // run_verification_safe_clients_silicon("verify_safe_clients", &filter);
    // save_verification_cache();
}
