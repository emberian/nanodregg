//! The parameters every module takes, built from [`crate::generated`] and nothing else.

use std::time::Duration;

use crate::frame::Limits;
use crate::generated as g;
use crate::mux::MuxLimits;
use crate::run::Table;

/// Frame bounds on both sockets.
pub const LIMITS: Limits = Limits {
    frame_bytes_max: g::FRAME_BYTES_MAX,
};

/// The supervisor's bounds.
pub const MUX: MuxLimits = MuxLimits {
    frame: LIMITS,
    connections_max: g::CONNECTIONS_MAX,
    idle: Duration::from_millis(g::IDLE_MS_MAX as u64),
    frame_deadline: Duration::from_millis(g::FRAME_MS_MAX as u64),
    reply: Duration::from_millis(g::REPLY_MS_MAX as u64),
    reply_write: Duration::from_millis(g::REPLY_WRITE_MS_MAX as u64),
};

/// What the step loop compares against.
pub const RUN: Table = Table {
    steps_max: g::STEPS_PER_COMMAND_MAX,
    sends_max: g::SENDS_MAX,
    submit: g::host_op::SUBMIT,
    lookup: g::host_op::LOOKUP,
    ok: g::status::OK,
    refused: g::status::REFUSED,
    absent: g::status::ABSENT,
    uncertain: g::status::UNCERTAIN,
};

/// `Bounds.replyMsMax`: how long either socket waits for one reply (PROTOCOL-20).
pub const REPLY: Duration = Duration::from_millis(g::REPLY_MS_MAX as u64);
