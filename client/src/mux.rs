//! The supervisor's core: many Unix-socket connections onto one Lean child's stdio.
//!
//! Client side, per connection: frames `u32le len ‖ op ‖ payload` (see [`crate::frame`]).
//! Child side: the same frame whose body is `u32le conn ‖ op ‖ payload` toward the child and
//! `u32le conn ‖ status ‖ payload` back. The mux parses no payload and decides nothing: a reply for
//! a connection that is gone is dropped (the client's recovery is lookup), and when the child closes
//! its stdout every connection is closed and [`serve`] returns, so the supervisor exits and the
//! service manager restarts the pair. There is exactly one restart path.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::Shutdown;
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::thread;

use crate::frame::{self, FrameError, Limits};

const CONN: usize = 4;

/// The mux's bounds, from the generated table.
#[derive(Clone, Copy, Debug)]
pub struct MuxLimits {
    /// The client-side frame bound; the child-side body adds the 4-byte connection id.
    pub frame: Limits,
    /// Open connections at once; one more is accepted and closed at once.
    pub connections_max: u32,
}

/// Why [`serve`] returned. Every end is the supervisor's exit.
#[derive(Debug)]
pub enum MuxEnd {
    /// The child closed its stdout.
    ChildClosed,
    /// The child wrote a frame the mux cannot route (shorter than a connection id and a status,
    /// or past the bound): the child is broken.
    ChildMalformed(FrameError),
    /// 2^32 connections were opened in this process; the mux closed the child's stdin so the
    /// child exits and the pair restarts with fresh ids.
    ConnectionIdsExhausted,
}

struct Shared<I> {
    /// `None` once the mux has closed the child's stdin.
    child_in: Mutex<Option<I>>,
    conns: Mutex<Conns>,
    exhausted: AtomicBool,
}

struct Conns {
    open: HashMap<u32, UnixStream>,
    next: Option<u32>,
}

fn lock<T>(m: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    // A poisoned lock means a thread panicked mid-update; the map and the pipe stay usable
    // (every update is a single insert/remove/write_all), so recover rather than cascade.
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Run the mux until the child closes. `child_in`/`child_out` are the child's stdin and stdout.
pub fn serve<I, O>(
    listener: UnixListener,
    child_in: I,
    mut child_out: O,
    limits: MuxLimits,
) -> MuxEnd
where
    I: Write + Send + 'static,
    O: Read,
{
    let shared = Arc::new(Shared {
        child_in: Mutex::new(Some(child_in)),
        conns: Mutex::new(Conns {
            open: HashMap::new(),
            next: Some(0),
        }),
        exhausted: AtomicBool::new(false),
    });
    let accepting = Arc::clone(&shared);
    thread::spawn(move || accept(&listener, &accepting, limits));
    let mut end = route(&mut child_out, &shared, limits);
    if matches!(end, MuxEnd::ChildClosed) && shared.exhausted.load(Ordering::SeqCst) {
        end = MuxEnd::ConnectionIdsExhausted;
    }
    for (_, stream) in lock(&shared.conns).open.drain() {
        let _ = stream.shutdown(Shutdown::Both);
    }
    end
}

fn accept<I: Write + Send + 'static>(
    listener: &UnixListener,
    shared: &Arc<Shared<I>>,
    limits: MuxLimits,
) {
    for stream in listener.incoming() {
        let Ok(stream) = stream else { continue };
        let Ok(writer) = stream.try_clone() else {
            continue;
        };
        let id = {
            let mut conns = lock(&shared.conns);
            match conns.next {
                _ if conns.open.len() >= limits.connections_max as usize => None,
                Some(id) => {
                    conns.next = id.checked_add(1);
                    conns.open.insert(id, writer);
                    Some(id)
                }
                None => None,
            }
        };
        let Some(id) = id else {
            let _ = stream.shutdown(Shutdown::Both);
            if lock(&shared.conns).next.is_none() && !shared.exhausted.swap(true, Ordering::SeqCst)
            {
                lock(&shared.child_in).take();
            }
            continue;
        };
        let shared = Arc::clone(shared);
        thread::spawn(move || {
            forward(id, stream, &shared, limits);
            if let Some(s) = lock(&shared.conns).open.remove(&id) {
                let _ = s.shutdown(Shutdown::Both);
            }
        });
    }
}

/// Client → child: each client frame becomes one child frame tagged with `id`.
fn forward<I: Write>(id: u32, mut stream: UnixStream, shared: &Shared<I>, limits: MuxLimits) {
    let child_max = limits.frame.frame_bytes_max.saturating_add(CONN as u32);
    while let Ok(f) = frame::read(&mut stream, limits.frame) {
        let mut child = lock(&shared.child_in);
        let Some(child) = child.as_mut() else { return };
        if frame::write_body(child, child_max, &[&id.to_le_bytes(), &[f.op], &f.payload]).is_err() {
            return;
        }
    }
}

/// Child → clients: route every reply by its connection id until the child closes.
fn route<I>(child_out: &mut impl Read, shared: &Shared<I>, limits: MuxLimits) -> MuxEnd {
    let child_max = limits.frame.frame_bytes_max.saturating_add(CONN as u32);
    loop {
        let body = match frame::read_body(child_out, child_max) {
            Ok(body) => body,
            Err(FrameError::Closed) => return MuxEnd::ChildClosed,
            Err(e) => return MuxEnd::ChildMalformed(e),
        };
        let Some((conn, rest)) = body.split_first_chunk::<CONN>() else {
            return MuxEnd::ChildMalformed(FrameError::Truncated {
                wanted: CONN + 1,
                got: body.len(),
            });
        };
        let Some((&status, payload)) = rest.split_first() else {
            return MuxEnd::ChildMalformed(FrameError::Truncated {
                wanted: CONN + 1,
                got: body.len(),
            });
        };
        let id = u32::from_le_bytes(*conn);
        let writer = lock(&shared.conns)
            .open
            .get(&id)
            .and_then(|s| s.try_clone().ok());
        if let Some(mut writer) = writer
            && frame::write(&mut writer, limits.frame, status, payload).is_err()
            && let Some(s) = lock(&shared.conns).open.remove(&id)
        {
            let _ = s.shutdown(Shutdown::Both);
        }
    }
}
