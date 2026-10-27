//! The child's end of the connector (`linux`): the descriptor `ND_CONNECTOR` names, claimed once.

use std::io;
use std::os::fd::{FromRawFd, OwnedFd};
use std::path::Path;
use std::sync::{Mutex, OnceLock, PoisonError};

use crate::linux::CONNECTOR_ENV;

/// The connector, one ask at a time (an ask is a send and its reply; two threads interleaving would
/// read each other's), with the count of replies owed to asks that timed out (`linux::ask`).
pub(crate) struct Connector(Mutex<(OwnedFd, u32)>);

impl Connector {
    pub(crate) fn ask(&self, path: &Path) -> io::Result<OwnedFd> {
        let mut held = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        let (fd, owed) = &mut *held;
        crate::linux::ask(fd, owed, path)
    }
}

/// The connector, if this process was launched with one. A malformed `ND_CONNECTOR`, or one naming
/// a descriptor that is not a seqpacket socket, is an error, never a plain connect.
pub(crate) fn get() -> io::Result<Option<&'static Connector>> {
    static C: OnceLock<Result<Option<Connector>, String>> = OnceLock::new();
    let c = C.get_or_init(|| {
        let Some(v) = std::env::var_os(CONNECTOR_ENV) else {
            return Ok(None);
        };
        let n: i32 = v
            .to_str()
            .and_then(|v| v.parse().ok())
            .filter(|n| *n > 2)
            .ok_or_else(|| format!("{CONNECTOR_ENV} is not a descriptor"))?;
        // SAFETY: the launcher (`linux::command`) left exactly this descriptor open across exec
        // and named it here; nothing else in this process opens it or knows its number, and it is
        // claimed once, so this OwnedFd is its only owner.
        #[allow(unsafe_code)]
        let fd = unsafe { OwnedFd::from_raw_fd(n) };
        match rustix::net::sockopt::socket_type(&fd) {
            Ok(rustix::net::SocketType::SEQPACKET) => Ok(Some(Connector(Mutex::new((fd, 0))))),
            _ => {
                // not ours to close: forget it rather than close a descriptor we do not own
                std::mem::forget(fd);
                Err(format!("{CONNECTOR_ENV}={n} is not a connector"))
            }
        }
    });
    c.as_ref()
        .map(Option::as_ref)
        .map_err(|e| io::Error::other(e.clone()))
}
