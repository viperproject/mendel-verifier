// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![deny(unused_must_use)]

// Import from `target/debug/build/viper-sys-<...>/out/import_wrappers.rs`
include!(concat!(env!("OUT_DIR"), "/import_wrappers.rs"));

// Dummy import to easily jump to the module using an IDE.
#[allow(unused_imports)]
use wrappers as _jump_to_wrappers;

use jni::{errors::Result, objects::JObject, JNIEnv};

pub fn get_system_out<'a>(env: &'a JNIEnv) -> Result<JObject<'a>> {
    env.get_static_field("java/lang/System", "out", "Ljava/io/PrintStream;")
        .and_then(|x| x.l())
}
