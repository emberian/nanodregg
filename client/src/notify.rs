//! The service manager's notification socket (systemd's `sd_notify` protocol, by hand: one datagram
//! of `KEY=VALUE` lines to `$NOTIFY_SOCKET`). keybroker sends `READY=1` once its sockets are bound
//! (OPS-22), so a `Type=notify` unit's dependents, the certifying writer, start only then.
//!
//! Without `$NOTIFY_SOCKET` (no service manager, a test, macOS) every call does nothing: liveness
//! is the manager's to ask for. The variable is read once, before any thread starts, and never
//! passed to a confined child (the sandbox clears the child's environment).

use std::io;
use std::os::unix::net::UnixDatagram;

/// Where to send, read once from the environment.
#[derive(Clone, Debug)]
pub struct Notify {
    /// `$NOTIFY_SOCKET`: a path, or `@name` for an abstract socket (Linux).
    at: String,
}

impl Notify {
    /// The manager's socket, if this process was started with one.
    pub fn from_env() -> Option<Self> {
        let at = std::env::var("NOTIFY_SOCKET").ok()?;
        (!at.is_empty()).then_some(Self { at })
    }

    /// Send one message (`READY=1`, `WATCHDOG=1`). A failed send is the caller's to ignore: the
    /// manager then restarts the unit on its watchdog, which is the point of asking.
    pub fn send(&self, msg: &str) -> io::Result<()> {
        let s = UnixDatagram::unbound()?;
        if let Some(name) = self.at.strip_prefix('@') {
            #[cfg(target_os = "linux")]
            {
                use std::os::linux::net::SocketAddrExt;
                let addr = std::os::unix::net::SocketAddr::from_abstract_name(name.as_bytes())?;
                s.send_to_addr(msg.as_bytes(), &addr)?;
                return Ok(());
            }
            #[cfg(not(target_os = "linux"))]
            {
                let _ = name;
                return Err(io::Error::other("abstract notify socket off Linux"));
            }
        }
        s.send_to(msg.as_bytes(), &self.at)?;
        Ok(())
    }
}
