//! A simple example demonstrating how to use StaticCell to distribute
//! Telemetry histograms.

#![feature(const_fn)]

extern crate telemetry;
extern crate atomic_cell;
extern crate rustc_serialize;

use std::thread;
use std::sync::mpsc::channel;

/// Definition of histograms.
mod hist {
    pub use atomic_cell::*;
    pub use telemetry::plain::*;

    /// Measure if we have shutdown correctly or as a consequence of a panic.
    pub static HAS_SHUTDOWN_CORRECTLY : StaticCell<Flag> = StaticCell::new();

    /// Measure the number of uses of each feature.
    pub static FOO_USAGE : StaticCell<Count> = StaticCell::new();
    pub static BAR_USAGE : StaticCell<Count> = StaticCell::new();
    pub static SNA_USAGE : StaticCell<Count> = StaticCell::new();
}

use hist::*;
fn main() {

    // Initialize Telemetry

    let telemetry = telemetry::Service::new(true);

    // In the future, the following may be delegated to a macro.
    let mut _guards = Vec::new(); // Histograms will be dropped when `_guards` is dropped.
    _guards.push(hist::HAS_SHUTDOWN_CORRECTLY.init(Flag::new(&telemetry, "HAS_SHUTDOWN_CORRECTLY".to_string())));
    _guards.push(hist::FOO_USAGE.init(Count::new(&telemetry, "FOO_USAGE".to_string())));
    _guards.push(hist::BAR_USAGE.init(Count::new(&telemetry, "BAR_USAGE".to_string())));
    _guards.push(hist::SNA_USAGE.init(Count::new(&telemetry, "SNA_USAGE".to_string())));

    // ...
    for i in 1 .. 10 {
        thread::spawn(move || {
            go(i);
        });
    }

    hist::HAS_SHUTDOWN_CORRECTLY.get().unwrap().record(());

    // Now look at the histograms.
    let (sender, receiver) = channel();
    telemetry.to_json(telemetry::Subset::AllPlain, telemetry::SerializationFormat::SimpleJson, sender.clone());
    let plain = receiver.recv().unwrap();
    print!("{}\n", plain.pretty());


    /* Prints:
    {
        "BAR_USAGE": ...,
        "FOO_USAGE": ...,
        "HAS_SHUTDOWN_CORRECTLY": 1,
        "SNA_USAGE": ...
    }
    */
}

// Dispatch to features, arbitrarily.
fn go(index: u32) {
    let mut total = 0;
    for j in 1 .. 2 * index {
        total += total + j + index;
        if j % 2 == 0 {
            feature_foo(total);
        }
        if j % 3 == 0 {
            let total = total;
            thread::spawn(move || {
                feature_sna(total);
            });
        }
        if j % 4 == 0 {
            feature_bar(total);
        }
    }
}


// The following features all modify histograms. We didn't have to
// pass the histograms as argument to each feature, cloning at each
// thread boundary. Hurray!
//
// This could, of course, be optimized to minimize the number of
// clones.
fn feature_foo(total: u32) {
    hist::FOO_USAGE.get().unwrap().record(total);
}

fn feature_sna(total: u32) {
    hist::SNA_USAGE.get().unwrap().record(total);
}

fn feature_bar(total: u32) {
    hist::BAR_USAGE.get().unwrap().record(total);
}
