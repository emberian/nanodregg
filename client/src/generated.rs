// @generated from Nanodregg.Protocol (Protocol/Table.lean) by Emit/Rust.lean. DO NOT EDIT.
// Regenerate: lake exe emit-rust client/src/generated.rs
// Check:      lake exe emit-rust --check client/src/generated.rs

pub const FRAME_BYTES_MAX: u32 = 262144;
pub const ARGV_BYTES_MAX: u32 = 65536;
pub const STEPS_PER_COMMAND_MAX: u32 = 64;
pub const SENDS_MAX: u32 = 8;
pub const CONNECTIONS_MAX: u32 = 64;

pub mod host_op {
    pub const SUBMIT: u8 = 1;
    pub const LOOKUP: u8 = 2;
    pub const READ: u8 = 3;
    pub const LOG: u8 = 4;
}

pub mod follow_op {
    pub const COMMAND: u8 = 5;
    pub const RESUME: u8 = 6;
}

pub mod status {
    pub const OK: u8 = 0;
    pub const REFUSED: u8 = 1;
    pub const UNCERTAIN: u8 = 2;
    pub const ABSENT: u8 = 3;
}

pub mod step {
    pub const DONE: u8 = 0;
    pub const SIGN: u8 = 1;
    pub const HOST: u8 = 2;
    pub const SUBMIT: u8 = 3;
}
