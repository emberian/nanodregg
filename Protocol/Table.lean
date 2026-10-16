/-
# Protocol.Table — the one operation table, as data

Two sockets, six operations. Everything a client or a supervisor needs to know about the wire is
on this page, and CODEC generates the Rust copy from it (law 2): op bytes, status bytes, step tags
and the four client bounds.

* `host.sock` (`host serve STORE`, the one writer): `submit`, `lookup`, `read`, `log`.
* `follow.sock` (`host follow STORE`, the member's own fold): `command`, `resume`.

What is NOT an operation, and where it went (minidregg's 186 opcodes, `DELETE-PROTOCOL-20261016.md`):
every family-specific plan/assemble/submit/lookup quadruple is one `submit`/`lookup` whose payload is
a signed call of some KIND (KERNEL's `Receive`; LANG's `install`/`invoke` are kinds, not ops); every
view is a `read` kind; challenge, prepare, assemble, author, inspect and signatures are steps of the
follow machine (Lean), not wire operations; describe/profile are a `read` kind; certify is the Host's
own seal; consent frames are `host follow` (HOST-7).

Each operation names the one function that answers it (`receiver`). The names are data until the
receiving layers commit those declarations; a gate then resolves each name in the environment.
-/
namespace Nanodregg.Protocol

/-- The two sockets of a deployment. -/
inductive Socket
  | host
  | follow
  deriving DecidableEq, Repr

/-- Whether answering an operation may append to the log. -/
inductive Effect
  | read
  | write
  deriving DecidableEq, Repr

/-- Every operation of the protocol. -/
inductive Op
  /-- a signed call: received into a Turn, admitted, appended; replies with the receipt -/
  | submit
  /-- the same signed call bytes: committed (receipt), absent, or never-admissible -/
  | lookup
  /-- a view of the writer's World, by kind; an authorized view carries a signature -/
  | read
  /-- the log's frames from a height: what a follower folds -/
  | log
  /-- a member's argv, parsed by the one command language -/
  | command
  /-- a continuation echoed back with the result of the step it asked for -/
  | resume
  deriving DecidableEq, Repr

namespace Op

def all : List Op := [submit, lookup, read, log, command, resume]

def code : Op → UInt8
  | submit => 1
  | lookup => 2
  | read => 3
  | log => 4
  | command => 5
  | resume => 6

def socket : Op → Socket
  | submit | lookup | read | log => .host
  | command | resume => .follow

def effect : Op → Effect
  | submit => .write
  | lookup | read | log | command | resume => .read

/-- The declaration that answers the operation. -/
def receiver : Op → String
  | submit => "Nanodregg.Kernel.Receive.receive"
  | lookup => "Nanodregg.Kernel.World.lookup"
  | read => "Nanodregg.Kernel.Receive.view"
  | log => "Nanodregg.Host.Log.framesFrom"
  | command => "Nanodregg.Protocol.Command.start"
  | resume => "Nanodregg.Protocol.Command.step"

/-- Decode a request byte; anything else is refused before a payload is read. -/
def ofCode? (b : UInt8) : Option Op := all.find? (·.code == b)

end Op

/-- The status byte of every reply on either socket. -/
inductive Status
  /-- answered; for `lookup`, committed -/
  | ok
  /-- refused by name; the payload is the refusal -/
  | refused
  /-- the writer cannot say whether the call committed (an append that did not read back) -/
  | uncertain
  /-- `lookup` only: the call is not in the log; resending the same bytes is safe -/
  | absent
  deriving DecidableEq, Repr

namespace Status

def all : List Status := [ok, refused, uncertain, absent]

def code : Status → UInt8
  | ok => 0
  | refused => 1
  | uncertain => 2
  | absent => 3

def ofCode? (b : UInt8) : Option Status := all.find? (·.code == b)

end Status

/-- The tag of a step the follow machine asks the client to perform (CLIENT-2). -/
inductive Step
  /-- print, exit; the command is over -/
  | done
  /-- sign exactly these bytes with custody's key -/
  | sign
  /-- send this frame to `host.sock` and resume with its reply -/
  | host
  /-- freeze this call as an attempt, settle it by submit/lookup, resume with the settlement -/
  | submit
  deriving DecidableEq, Repr

namespace Step

def all : List Step := [done, sign, host, submit]

def code : Step → UInt8
  | done => 0
  | sign => 1
  | host => 2
  | submit => 3

def ofCode? (b : UInt8) : Option Step := all.find? (·.code == b)

end Step

/-! The bounds the client and the supervisor enforce before allocating. -/
namespace Bounds

/-- One frame body (op or status byte and payload), either socket, either direction. -/
def frameBytesMax : Nat := 262144
/-- A `command` payload: the argv, `4 + Σ (4 + len)`. -/
def argvBytesMax : Nat := 65536
/-- Steps one command may take before follow ends it with a refusal. -/
def stepsPerCommandMax : Nat := 64
/-- Sends of one frozen call: the first submit and the resends after `absent`. -/
def sendsMax : Nat := 8
/-- Connections one `nd-supervise` holds open at once (either socket). It bounds the supervisor's
memory: each connection buffers at most one frame per direction, so the whole mux holds at most
`2 * connectionsMax * frameBytesMax` bytes (32 MiB). A deployment's members are friends, not the
public: past the bound the supervisor stops accepting, and the client sees a refused connect. -/
def connectionsMax : Nat := 64

end Bounds

end Nanodregg.Protocol
