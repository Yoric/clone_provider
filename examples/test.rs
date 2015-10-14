#[macro_use]
extern crate lazy_static;

extern crate clone_provider;

pub use clone_provider::*;

use std::sync::mpsc::{channel, Sender};
use std::thread;

// We need lazy_static! for the sake of `Arc`. Note that the
// `AtomicPtr` is actually never deallocated, but that's probably
// ok. We could probably do without that by replacing `store` of
// `Guard` by a `&CloneProvider`.

lazy_static!(
    static ref PROVIDER : CloneProvider<MySender> =
        CloneProvider::new();
);

#[derive(Clone)]
struct MySender(Sender<bool>);
impl SyncClone for MySender {}
impl MySender {
    fn send(&self, value: bool) {
        let &MySender(ref sender) = self;
        sender.send(value).unwrap();
    }
}

fn main() {
  let chan = channel();
  let sender = Box::new(MySender(chan.0));
  let _guard = PROVIDER.attach(sender);

  for _ in 1 .. 10 {
    let copy = PROVIDER.get().unwrap();
    thread::spawn(move || {
       copy.send(true);
    });
  }
}
