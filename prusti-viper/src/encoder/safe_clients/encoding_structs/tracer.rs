// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{io::Write, cell::RefCell, sync::atomic::{AtomicUsize, Ordering}};
use prusti_common::report;
use vir_crate::common::graphviz::escape_html;
pub use crate::encoder::safe_clients::prelude::*;
use std::cell::LazyCell;

static TRACER_THREAD: AtomicUsize = AtomicUsize::new(0);
thread_local! {
    pub static TRACER: LazyCell<Tracer>  = LazyCell::new(|| {
        // Build lazily, so that we can read `config::dump_debug_info()`.
        Tracer::new("tracer", format!("global_{}", TRACER_THREAD.fetch_add(1, Ordering::SeqCst)))
    });
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TraceFrameId(usize);

impl !Send for TraceFrameId {}

impl TraceFrameId {
    pub fn dummy() -> Self {
        TraceFrameId(0)
    }
}

impl Drop for TraceFrameId {
    fn drop(&mut self) {
        if cfg!(debug_assertions) {
            TRACER.with(|tracer| {
                tracer.close(self, "<none> (drop)");
            });
        }
    }
}

pub struct Tracer {
    name: String,
    open_calls: RefCell<Vec<usize>>,
    writer: Option<RefCell<Box<dyn Write>>>,
}

impl Tracer {
    pub fn new(namespace: &str, name: impl ToString) -> Self {
        let name = format!("{}.html", name.to_string());
        let writer = if config::dump_debug_info() {
            Some(RefCell::new(report::log::build_writer(namespace, name.clone()).unwrap()))
        } else {
            None
        };
        let this = Tracer {
            name,
            open_calls: RefCell::new(vec![]),
            writer,
        };
        this.write_header().unwrap_or_else(
            |err| panic!("failed to write trace to {:?}: {:?}", this.name, err)
        );
        this
    }

    pub fn open(&self, context: impl ToString, function: impl ToString, args: impl ToString) -> TraceFrameId {
        let mut open_calls = self.open_calls.borrow_mut();
        let frame_id = TraceFrameId(1 + open_calls.len());
        open_calls.push(frame_id.0);
        drop(open_calls);
        self.write_open(context, function, args).unwrap_or_else(
            |err| panic!("failed to write trace to {:?}: {:?}", self.name, err)
        );
        frame_id
    }

    pub fn close(&self, frame_id: &TraceFrameId, result: impl ToString) {
        let mut open_calls = self.open_calls.borrow_mut();
        while open_calls.last().copied().iter().any(|&v| v > frame_id.0) {
            let frame = open_calls.pop();
            self.write_close("<none> (unclosed)").unwrap_or_else(
                |err| panic!("failed to write trace to {:?}: {:?}", self.name, err)
            );
        }
        let Some(_) = open_calls.pop() else {
            error!(
                "Tried to pop inexistent {frame_id:?} while tracing the translation {:?}",
                self.name,
            );
            return;
        };
        drop(open_calls);
        self.write_close(result).unwrap_or_else(
            |err| panic!("failed to write trace to {:?}: {:?}", self.name, err)
        );
    }

    fn write_header(&self) -> std::io::Result<()> {
        let mut writer = match self.writer {
            Some(ref w) => w.borrow_mut(),
            None => return Ok(()),
        };
        writeln!(writer,
            "<style>\n\
            details.frame {{\n\
                background-color: rgba(147, 193, 211, 0.075);\n\
                border: 1px solid gray;\n\
                margin: 0px 0px 10px 10px;\n\
            }}\n\
            .frame>summary {{\n\
                padding: 10px 0px 10px 10px;\n\
                cursor: pointer;\n\
            }}\n\
            .result {{\n\
                padding: 0px 0px 10px 10px;\n\
            }}\n\
            .context {{ display: none; }}\n\
            </style>"
        )?;
        writeln!(writer,
            "<h1>Trace of <code>{}</code></h1>",
            escape_html(&self.name),
        )?;
        Ok(())
    }

    fn write_open(&self, context: impl ToString, function: impl ToString, args: impl ToString) -> std::io::Result<()> {
        let mut writer = match self.writer {
            Some(ref w) => w.borrow_mut(),
            None => return Ok(()),
        };
        writeln!(writer,
            "<details class='frame'><summary>\
            <div class='context'>Context: <code>{}</code></div>\
            <div class='function'>Function: <code>{}</code></div>\
            <div class='args'>Args: <code>{}</code></div></summary>",
            escape_html(context),
            escape_html(function),
            escape_html(args),
        )?;
        Ok(())
    }

    fn write_close(&self, result: impl ToString) -> std::io::Result<()> {
        let mut writer = match self.writer {
            Some(ref w) => w.borrow_mut(),
            None => return Ok(()),
        };
        writeln!(writer,
            "<details class='result'><summary>Result:</summary><pre>\n{}\n</pre></details></details>",
            escape_html(result),
        )?;
        Ok(())
    }
}

impl Drop for Tracer {
    fn drop(&mut self) {
        let mut open_calls = self.open_calls.borrow_mut();
        while open_calls.pop().is_some() {
            self.write_close("<none>").unwrap_or_else(
                |err| panic!("failed to write trace to {:?}: {:?}", self.name, err)
            );
        }
    }
}

#[macro_export]
macro_rules! open_trace {
    ($self:expr, $function:expr, $args:expr) => {{
        log::trace!("[open] {}: {}", $function, $args);
        if cfg!(debug_assertions) {
            $crate::encoder::safe_clients::encoding_structs::TRACER.with(|t|
                t.open(format!("{:?} {:?}", $self.def_id(), $self.substs()), $function, $args)
            )
        } else {
            $crate::encoder::safe_clients::encoding_structs::TraceFrameId::dummy()
        }
    }};
    ($function:expr, $args:expr) => {{
        log::trace!("[open] {}: {}", $function, $args);
        if cfg!(debug_assertions) {
            $crate::encoder::safe_clients::encoding_structs::TRACER.with(|t|
                t.open("<none>", $function, $args)
            )
        } else {
            $crate::encoder::safe_clients::encoding_structs::TraceFrameId::dummy()
        }
    }};
}

#[macro_export]
macro_rules! close_trace {
    ($frame:expr, $result:expr) => {
        if cfg!(debug_assertions) {
            $crate::encoder::safe_clients::encoding_structs::TRACER.with(
                |t| t.close(&$frame, $result)
            );
        }
        std::mem::forget($frame);
    };
    ($self:expr, $frame:expr, $result:expr) => {
        close_trace!($frame, $result)
    };
}
