//! The parameters every module takes, built from [`crate::generated`] and nothing else.

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
};
