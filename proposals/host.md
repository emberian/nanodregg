# proposals/host.md — what HOST needs from KERNEL, CODEC and PROTOCOL (BUILD-HOST, 2026-10-16)

Signatures, not prose. Each is the *least* the Host can be written against; an owner who commits a
different shape wins, and the Host adapts. Names are proposals.

## From KERNEL

```lean
namespace Nanodregg.Kernel
structure World            -- opaque to the Host; the Host never reads a field except through below
structure Turn
inductive Reject           -- named constructors; the Host renders them, never interprets them

def World.admit  : World → Turn → Except Reject World      -- THE receive path (law 1)
def World.height : World → UInt64
def World.chain  : World → Digest                          -- the log chain at `height`
def World.root   : World → Digest
def World.genesis : Genesis → Except Reject World          -- or genesis as the first Turn: KERNEL's call

-- what the Host asserts in pairs (law 4); the Host needs these as theorems to cite at each assert
theorem admit_height  : World.admit w t = .ok w' → w'.height = w.height + 1
theorem admit_chain   : World.admit w t = .ok w' → w'.chain = chainStep w.chain (Turn.digest t)
```

Host relies on `admit` being a *function* (determinism is then free) and fail-closed (a refused
Turn leaves the World unchanged: it returns `.error`, there is no partial state to roll back).

The follower and the consent provider call exactly `World.admit` on decoded log Turns. If KERNEL
splits "admit a request" from "fold a logged Turn", there are two paths and law 1 is broken:
**the logged Turn must be the thing `admit` takes**.

## From CODEC

```lean
namespace Nanodregg.Codec
structure Digest where bytes : ByteArray; size_eq : bytes.size = 32
structure Codec (α : Type) where
  encode  : α → ByteArray
  decodeAt : ByteArray → (off : Nat) → Except DecodeError (α × Nat)   -- one pass, by offset
  decode_encode : ∀ a b off, decodeAt (b ++ encode a) b.size = .ok (a, b.size + (encode a).size)  -- shape TBD by CODEC
  canonical     : ∀ bytes off a n, decodeAt bytes off = .ok (a, n) → bytes.extract off n = encode a

def u32le : Codec UInt32
def u64le : Codec UInt64
def mac  : MacKey → ByteArray → Digest     -- KMAC256 or BLAKE3-keyed: CODEC's call
Turn.codec  : Codec Kernel.Turn
World.codec : Codec Kernel.World           -- the checkpoint IS this encoding
```

Until CODEC commits `u32le`/`u64le`, `Host/Log` frames with its own two little-endian helpers in
one private section, marked for deletion the day `Codec.Stream` lands (a twin with an expiry date,
recorded in DECISIONS HOST-5).

## From PROTOCOL

```lean
namespace Nanodregg.Protocol
inductive Kind | pure | read | write
structure Request where conn : UInt32; op : UInt8; payload : ByteArray
inductive Answer
  | reply (bytes : ByteArray)
  | refused (name : Refusal)
  | admit (turn : Kernel.Turn) (receipt : Kernel.World → ByteArray)  -- reply built from the post-World
structure Op where
  code    : UInt8
  bound   : Nat                       -- max payload bytes; past it the Host refuses `pastBound`
  kind    : Kind
  handle  : Kernel.World → ByteArray → Answer
def table : Array Op
theorem table_codes_unique : (table.map Op.code).toList.Nodup
def find? (op : UInt8) : Option Op
```

`handle` is where minidregg's ~400 receiver modules went. **Open question for ROOT (charter
gap):** the table names receivers but no layer row owns *request → Turn* (authority, law,
funding checks). HOST's proposal: KERNEL owns the decision functions (`Kernel.Receive.*`),
PROTOCOL's table binds an opcode to one of them; HOST owns neither.

## What HOST commits for others

```lean
namespace Nanodregg.Host
def admitBatch (admit : W → T → Except R W) (handle : W → Q → Answer W T R) :
    W → Array Q → W × Array (Pending W T R)          -- pure; the loop's whole decision
theorem admitBatch_flatten : (admitBatch … w (a ++ b)).1 = (admitBatch … (admitBatch … w a).1 b).1
structure BatchFrame where firstHeight : UInt64; turns : Array ByteArray; chain : ByteArray
def Log.encode : MacKey → (prevTag : ByteArray) → BatchFrame → ByteArray
def Log.recover : … → ByteArray → Recovered      -- frames + valid length + named tail verdict
```
The client (BUILD-CLIENT) needs only the frame shape `u32 len ‖ u32 conn ‖ u8 op ‖ payload` and
the reply shape `u32 len ‖ u32 conn ‖ u8 status ‖ payload`, `status ∈ {0 ok, 1 refused, 2 uncertain, 3 absent}` (HOST-8).

## The step protocol `host follow` ⇄ `nd` (HOST-9, with PROTOCOL)

```lean
namespace Nanodregg.Host.Follow
inductive Step where
  | done   (exit : UInt8) (stdout stderr : ByteArray)
  | sign   (message : ByteArray) (k : ByteArray)          -- custody signs `message` with the member key
  | host   (op : UInt8) (payload : ByteArray) (k : ByteArray)
  | submit (call : ByteArray) (k : ByteArray)              -- an attempt: custody's frozen submit/lookup loop
inductive Result where
  | signature (bytes : ByteArray) | reply (status : UInt8) (bytes : ByteArray) | settled (status : UInt8) (bytes : ByteArray)
def command : World → Array String → Except Refusal Step
def resume  : World → (k : ByteArray) → Result → Except Refusal Step     -- `k` decoded canonically, ≤ continuationBytesMax
theorem resume_rederives : …   -- the next `sign` message is a function of (World, command, step index)
```
Wire: `nd → follow`: `u32 len ‖ u8 tag(command=0|resume=1) ‖ body`; `follow → nd`: `u32 len ‖ u8 step ‖ body`.
Tags and bounds come from PROTOCOL's generated table.
