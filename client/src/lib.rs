//! The member's side of nanodregg: custody (the seed, the frozen attempts), transport (frames
//! over a socket) and the workspace on disk.
//!
//! This crate decides nothing. Its only protocol knowledge is the table the codec layer generates
//! (operation numbers, bounds, outcome kinds); until that table exists, every function here takes
//! the values it needs as parameters and the crate has no binary.

pub mod attempt;
pub mod custody;
pub mod frame;
mod fsx;
pub mod mux;
