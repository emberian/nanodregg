//! The supervisor's core: many Unix-socket connections onto one Lean child's stdio.
//!
//! Client side, per connection: frames `u32le len ‖ op ‖ payload` (see [`crate::frame`]).
//! Child side: the same frame whose body is `u32le conn ‖ op ‖ payload` toward the child and
//! `u32le conn ‖ status ‖ payload` back. The mux parses no payload and decides nothing about a
//! request: a reply for a connection that is gone is dropped (the client's recovery is lookup),
//! and when the child closes its stdout every connection is closed and [`serve`] returns, so the
//! supervisor exits and the service manager restarts the pair. There is exactly one restart path.
//!
//! What the mux does decide is when a CONNECTION ends, with Lean's numbers and Lean's names
//! (`Protocol.Bounds`, `Protocol.CloseReason`, emitted into [`crate::generated`]):
//! - each connection has its own writer thread fed one reply at a time, so a peer that stops
//!   reading is closed `replyBacklog` and never stalls the routing of anyone else's replies;
//! - a connection is `idle` only when it is silent at a frame boundary with no request in flight;
//!   a request in flight longer than `REPLY_MS_MAX` is `replyTimeout` (a Host that loses a reply
//!   must not wedge the connection forever); a started frame must finish within `FRAME_MS_MAX`;
//! - every close is named to the peer: one frame `status::CLOSED ‖ CloseReason::name()`, written
//!   best-effort by the connection's writer (one writer per stream, so frames never interleave),
//!   then the stream is shut down. The over-the-bound connection is answered `full` the same way,
//!   and a `closed` reply from the child (`nd-attach` relaying a remote close) ends the connection.
//!
//! `conn` is a counter, never an identity.

use std::collections::{HashMap, VecDeque};
use std::io::{self, ErrorKind, Read, Write};
use std::net::Shutdown;
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{Receiver, SyncSender, TrySendError, sync_channel};
use std::sync::{Arc, Mutex, PoisonError};
use std::thread;
use std::time::{Duration, Instant};

use crate::frame::{self, FrameError, Limits};
use crate::generated::{self as g, CloseReason, status};

const CONN: usize = 4;

/// The mux's bounds, from the generated table.
#[derive(Clone, Copy, Debug)]
pub struct MuxLimits {
    /// The client-side frame bound; the child-side body adds the 4-byte connection id.
    pub frame: Limits,
    /// Open connections at once; one more is answered `full` and closed.
    pub connections_max: u32,
    /// Silent at a frame boundary with nothing in flight this long: `idle`.
    pub idle: Duration,
    /// A started frame must be complete within this: `frameStalled`.
    pub frame_deadline: Duration,
    /// A request with no reply this long: `replyTimeout`.
    pub reply: Duration,
    /// One write to the peer must complete within this: `replyWriteFailed`.
    pub reply_write: Duration,
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

/// What a connection's writer is handed.
enum Out {
    Reply(Vec<u8>),
    /// The connection's last frame (a `closed` frame), after which the stream is shut down.
    Last(Vec<u8>),
}

struct Conn {
    /// A handle on the stream for shutting it down (the writer owns its own clone).
    stream: UnixStream,
    out: SyncSender<Out>,
    /// A reply is queued and not yet taken by the writer: the one slot is full.
    slot: AtomicBool,
    /// When each request in flight was forwarded, oldest first; and when the connection last
    /// became quiet (nothing in flight, nothing being read).
    flight: Mutex<(VecDeque<Instant>, Instant)>,
    /// The writer thread, joined when the mux ends so queued replies reach the peer.
    writer: Mutex<Option<thread::JoinHandle<()>>>,
    /// Why the mux ended this connection, owed to the child as a hang-up (PROTOCOL-23); unset
    /// when the child itself closed it.
    hang: Mutex<Option<CloseReason>>,
}

struct Shared<I> {
    /// `None` once the mux has closed the child's stdin.
    child_in: Mutex<Option<I>>,
    conns: Mutex<Conns>,
    exhausted: AtomicBool,
}

struct Conns {
    open: HashMap<u32, Arc<Conn>>,
    next: Option<u32>,
}

fn lock<T>(m: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    // A poisoned lock means a thread panicked mid-update; every update is a single
    // insert/remove/push/write_all, so recover rather than cascade.
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

impl<I> Shared<I> {
    /// End connection `id` once: forget it, stop its reader, and hand its writer the named close
    /// (`None`: the peer is already gone, nothing to say).
    fn close(&self, id: u32, why: Option<CloseReason>) {
        if let Some(c) = lock(&self.conns).open.get(&id) {
            *lock(&c.hang) = Some(why.unwrap_or(CloseReason::PeerLeft));
        }
        self.end(id, why.map(close_frame));
    }

    /// End connection `id` once, its last frame being `last` (if any).
    fn end(&self, id: u32, last: Option<Vec<u8>>) {
        let Some(c) = lock(&self.conns).open.remove(&id) else {
            return;
        };
        let _ = c.stream.shutdown(Shutdown::Read);
        let said = last.is_some_and(|b| c.out.try_send(Out::Last(b)).is_ok());
        if !said {
            let _ = c.stream.shutdown(Shutdown::Both);
        }
    }
}

/// The frame that names a close.
fn close_frame(r: CloseReason) -> Vec<u8> {
    let name = r.name().as_bytes();
    let mut b = Vec::with_capacity(5 + name.len());
    b.extend_from_slice(
        &u32::try_from(1 + name.len())
            .unwrap_or(u32::MAX)
            .to_le_bytes(),
    );
    b.push(status::CLOSED);
    b.extend_from_slice(name);
    b
}

/// Write `bytes` within `limit`, then flush.
fn write_within(w: &mut UnixStream, limit: Duration, bytes: &[u8]) -> io::Result<()> {
    w.set_write_timeout(Some(limit))?;
    w.write_all(bytes)?;
    w.flush()
}

/// Run the mux until the child closes. `child_in`/`child_out` are the child's stdin and stdout.
pub fn serve<I, O>(listener: UnixListener, child_in: I, child_out: O, limits: MuxLimits) -> MuxEnd
where
    I: Write + Send + 'static,
    O: Read,
{
    serve_admitting(listener, child_in, child_out, limits, None)
}

/// [`serve`], admitting only connections whose peer is `peer = (uid, gid)` (`SO_PEERCRED`,
/// HOSTING-20); any other is closed `peerRefused` before a frame is read or a connection id spent.
pub fn serve_admitting<I, O>(
    listener: UnixListener,
    child_in: I,
    mut child_out: O,
    limits: MuxLimits,
    peer: Option<(u32, u32)>,
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
    thread::spawn(move || accept(&listener, &accepting, limits, peer));
    let mut end = route(&mut child_out, &shared, limits);
    if matches!(end, MuxEnd::ChildClosed) && shared.exhausted.load(Ordering::SeqCst) {
        end = MuxEnd::ConnectionIdsExhausted;
    }
    // The child is gone: every connection ends after the replies already queued for it (each
    // write is bounded by `reply_write`, so the joins are bounded too).
    let open: Vec<(u32, Arc<Conn>)> = lock(&shared.conns)
        .open
        .iter()
        .map(|(i, c)| (*i, Arc::clone(c)))
        .collect();
    for (id, _) in &open {
        shared.end(*id, Some(Vec::new()));
    }
    for (_, c) in open {
        if let Some(w) = lock(&c.writer).take() {
            let _ = w.join();
        }
    }
    end
}

fn accept<I: Write + Send + 'static>(
    listener: &UnixListener,
    shared: &Arc<Shared<I>>,
    limits: MuxLimits,
    peer: Option<(u32, u32)>,
) {
    for stream in listener.incoming() {
        let Ok(mut stream) = stream else { continue };
        if let Some(p) = peer
            && nanodregg_sandbox::custody::peer_cred(&stream).ok() != Some(p)
        {
            let close = close_frame(CloseReason::PeerRefused);
            let _ = write_within(&mut stream, limits.reply_write, &close);
            let _ = stream.shutdown(Shutdown::Both);
            continue;
        }
        let (Ok(writer), Ok(handle)) = (stream.try_clone(), stream.try_clone()) else {
            continue;
        };
        // Two slots: at most one reply (the `slot` flag) and the one close.
        let (tx, rx) = sync_channel(2);
        let conn = Arc::new(Conn {
            stream: handle,
            out: tx,
            slot: AtomicBool::new(false),
            flight: Mutex::new((VecDeque::new(), Instant::now())),
            writer: Mutex::new(None),
            hang: Mutex::new(None),
        });
        let id = {
            let mut conns = lock(&shared.conns);
            match conns.next {
                _ if conns.open.len() >= limits.connections_max as usize => None,
                Some(id) => {
                    conns.next = id.checked_add(1);
                    conns.open.insert(id, Arc::clone(&conn));
                    Some(id)
                }
                None => None,
            }
        };
        let Some(id) = id else {
            let _ = write_within(
                &mut stream,
                limits.reply_write,
                &close_frame(CloseReason::Full),
            );
            let _ = stream.shutdown(Shutdown::Both);
            if lock(&shared.conns).next.is_none() && !shared.exhausted.swap(true, Ordering::SeqCst)
            {
                lock(&shared.child_in).take();
            }
            continue;
        };
        let sh = Arc::clone(shared);
        let c = Arc::clone(&conn);
        let w = thread::spawn(move || write_loop(id, writer, &rx, &c, &sh, limits));
        *lock(&conn.writer) = Some(w);
        let sh = Arc::clone(shared);
        thread::spawn(move || {
            let why = forward(id, stream, &conn, &sh, limits);
            sh.close(id, why);
            // The connection's reader is the one thread that writes its frames to the child, so
            // the hang-up follows its last request.
            if let Some(r) = lock(&conn.hang).take()
                && let Some(child) = lock(&sh.child_in).as_mut()
            {
                let max = limits.frame.frame_bytes_max.saturating_add(CONN as u32);
                let _ = frame::write_body(
                    child,
                    max,
                    &[&id.to_le_bytes(), &[g::HANGUP], r.name().as_bytes()],
                );
            }
        });
    }
}

/// The connection's one writer: replies in order, then (if any) the named close.
fn write_loop<I>(
    id: u32,
    mut w: UnixStream,
    rx: &Receiver<Out>,
    c: &Conn,
    sh: &Shared<I>,
    limits: MuxLimits,
) {
    while let Ok(out) = rx.recv() {
        match out {
            Out::Reply(bytes) => {
                c.slot.store(false, Ordering::SeqCst);
                if write_within(&mut w, limits.reply_write, &bytes).is_err() {
                    sh.close(id, Some(CloseReason::ReplyWriteFailed));
                }
            }
            Out::Last(bytes) => {
                let _ = write_within(&mut w, limits.reply_write, &bytes);
                let _ = w.shutdown(Shutdown::Both);
                return;
            }
        }
    }
}

/// A reader that fails `TimedOut` once `until` has passed, however the bytes trickle in.
struct Deadline<'a> {
    s: &'a UnixStream,
    until: Instant,
}

impl Read for Deadline<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let left = self.until.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(ErrorKind::TimedOut.into());
        }
        self.s.set_read_timeout(Some(left))?;
        self.s.read(buf)
    }
}

fn timed_out(e: &io::Error) -> bool {
    matches!(e.kind(), ErrorKind::WouldBlock | ErrorKind::TimedOut)
}

/// Client → child: each client frame becomes one child frame tagged with `id`. Returns why the
/// connection ends (`None`: the peer left or the child is gone).
fn forward<I: Write>(
    id: u32,
    s: UnixStream,
    c: &Conn,
    sh: &Shared<I>,
    limits: MuxLimits,
) -> Option<CloseReason> {
    let child_max = limits.frame.frame_bytes_max.saturating_add(CONN as u32);
    // The boundary wait wakes at least this often to judge `idle` and `replyTimeout`.
    let tick = limits.idle.min(limits.reply) / 4;
    let mut first = [0u8; 1];
    loop {
        if s.set_read_timeout(Some(tick.max(Duration::from_millis(1))))
            .is_err()
        {
            return None;
        }
        match (&s).read(&mut first) {
            Ok(0) => return None,
            Ok(_) => {}
            Err(e) if timed_out(&e) => {
                let flight = lock(&c.flight);
                match flight.0.front() {
                    Some(t) if t.elapsed() >= limits.reply => {
                        return Some(CloseReason::ReplyTimeout);
                    }
                    Some(_) => continue,
                    None if flight.1.elapsed() >= limits.idle => return Some(CloseReason::Idle),
                    None => continue,
                }
            }
            Err(_) => return None,
        }
        let started = Instant::now();
        let mut rest = Deadline {
            s: &s,
            until: started + limits.frame_deadline,
        };
        let f = match frame::read(&mut (&first[..]).chain(&mut rest), limits.frame) {
            Ok(f) => f,
            Err(FrameError::Io(e)) if timed_out(&e) => return Some(CloseReason::FrameStalled),
            Err(FrameError::Closed | FrameError::Io(_) | FrameError::Truncated { .. }) => {
                return None;
            }
            Err(FrameError::Empty | FrameError::PastBound { .. }) => {
                return Some(CloseReason::FrameRefused);
            }
        };
        if f.op == g::HANGUP {
            return Some(CloseReason::FrameRefused); // the child wire's byte, never a client's
        }
        {
            let mut flight = lock(&c.flight);
            flight.0.push_back(Instant::now());
            flight.1 = Instant::now();
        }
        let mut child = lock(&sh.child_in);
        let child = child.as_mut()?;
        if frame::write_body(child, child_max, &[&id.to_le_bytes(), &[f.op], &f.payload]).is_err() {
            return None;
        }
    }
}

/// Child → clients: route every reply by its connection id until the child closes. Never blocks
/// on a peer: a reply goes into its connection's one slot or the connection is closed.
fn route<I>(child_out: &mut impl Read, shared: &Shared<I>, limits: MuxLimits) -> MuxEnd {
    // `conn ‖ status ‖ payload`: the client-side bound plus the connection id, so what is
    // forwarded (`status ‖ payload`) is within the client's bound.
    let child_max = limits.frame.frame_bytes_max.saturating_add(CONN as u32);
    loop {
        let body = match frame::read_body(child_out, child_max) {
            Ok(body) => body,
            Err(FrameError::Closed) => return MuxEnd::ChildClosed,
            Err(e) => return MuxEnd::ChildMalformed(e),
        };
        let (Some((conn, rest)), true) = (body.split_first_chunk::<CONN>(), body.len() > CONN)
        else {
            return MuxEnd::ChildMalformed(FrameError::Truncated {
                wanted: CONN + 1,
                got: body.len(),
            });
        };
        let id = u32::from_le_bytes(*conn);
        let Some(c) = lock(&shared.conns).open.get(&id).cloned() else {
            continue;
        };
        {
            let mut flight = lock(&c.flight);
            // Replies come back in request order per connection (one loop, FIFO per conn); if a
            // Host ever reordered them the oldest stamp would be dropped first, which only makes
            // `replyTimeout` later, never sooner.
            flight.0.pop_front();
            if flight.0.is_empty() {
                flight.1 = Instant::now();
            }
        }
        let mut bytes = Vec::with_capacity(4 + rest.len());
        bytes.extend_from_slice(&u32::try_from(rest.len()).unwrap_or(u32::MAX).to_le_bytes());
        bytes.extend_from_slice(rest);
        if rest[0] == status::CLOSED {
            // A `closed` from upstream (nd-attach relaying the box's supervisor) ends this
            // connection here too: it is delivered as the connection's last frame.
            shared.end(id, Some(bytes));
            continue;
        }
        if c.slot.swap(true, Ordering::SeqCst) {
            shared.close(id, Some(CloseReason::ReplyBacklog));
            continue;
        }
        match c.out.try_send(Out::Reply(bytes)) {
            Ok(()) => {}
            Err(TrySendError::Full(_) | TrySendError::Disconnected(_)) => {
                shared.close(id, Some(CloseReason::ReplyBacklog));
            }
        }
    }
}
