/-
# Host.Sock — the client end of a Unix stream socket (`Host/c/sock.c`, HOST-52)

A connection behind an opaque handle; the descriptor closes when the handle is freed. Every call is
bounded by the connection's timeout. Every failure is an `IO` error that names it: `timeout`,
`pathNul`, `pathEmpty`, `pathTooLong` (the path does not fit `sun_path`; refused before a byte is
copied), `timeoutZero`, `readMaxZero`, `readMaxPastBound`, or the call and its errno
(`connect: … (errno 2)`, a peer that shut its reading side `send: … (errno 32)`). EINTR is retried
on what is left of the deadline, never reported. `read` returns at least one byte, or none exactly
at end of stream. A `timeout` is an IO exception, not an empty read: a reader over `Conn.stream`
(`Host.readExact`) lets it escape, so its caller catches it and names it.

This is THE client end of a Unix socket in the tree: a Lean process that connects to one uses it,
and a future Host serve extends `sock.c` rather than adding a second socket C file (HOST-52).

HOSTING's resident is the first user (HOSTING-27): Lean 4.30 has no AF_UNIX. Host's own serving
goes through `nd-supervise`'s pipes today and may adopt this later. Linked into the executables
only; nothing proved depends on what these calls return.
-/

namespace Nanodregg.Host

opaque ConnPointed : NonemptyType
/-- An open, connected Unix stream socket and its per-call timeout. -/
def Conn : Type := ConnPointed.type
instance : Nonempty Conn := ConnPointed.property

/-- Connect to the socket at `path`, every later call on it bounded by `timeoutMs`. -/
@[extern "nd_unix_connect"] opaque Conn.connect (path : @& String) (timeoutMs : UInt32) : IO Conn
/-- Send every byte, or fail. -/
@[extern "nd_conn_write_all"] opaque Conn.writeAll (c : @& Conn) (bytes : @& ByteArray) : IO Unit
/-- Between 1 and `max` bytes, or none at end of stream (`max` = 0 is refused `readMaxZero`). -/
@[extern "nd_conn_read"] opaque Conn.read (c : @& Conn) (max : USize) : IO ByteArray

/-- The connection as a stream, so the readers written over `IO.FS.Stream` (`Host.readExact`) read
it unchanged. It has no lines and no flush: nothing is buffered. -/
def Conn.stream (c : Conn) : IO.FS.Stream where
  flush := pure ()
  read := c.read
  write := c.writeAll
  getLine := throw (IO.userError "Conn: no lines")
  putStr s := c.writeAll s.toUTF8
  isTty := pure false

end Nanodregg.Host
