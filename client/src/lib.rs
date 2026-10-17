//! The member's side of nanodregg: custody (the seed, the frozen attempts), transport (frames
//! over a socket) and the workspace on disk, plus the supervisor that puts a Lean child behind a
//! Unix socket.
//!
//! This crate decides nothing. Its only protocol knowledge is [`generated`], emitted from
//! `Protocol/Table.lean`; the library functions take the values they need as parameters and
//! [`table`] builds those parameters from the generated file, nowhere else.

pub mod attempt;
pub mod custody;
pub mod frame;
mod fsx;
#[allow(missing_docs)] // emitted by Emit/Rust.lean; never edited by hand
pub mod generated;
pub mod mux;
pub mod run;
pub mod sockets;
pub mod table;
