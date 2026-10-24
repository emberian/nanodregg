import Protocol.Table
import Codec.Layout

/-!
# Protocol.Frames — the follow socket's payloads as codecs

Each payload's layout is data in `Protocol.Table`. This module turns it into the one codec
(`Codec.Layout.codec`), and `Emit.Rust` prints the Rust reader and writer from the same data, so the
client holds no hand-written copy (CLIENT-10). Canonicity: `Protocol.Proofs.Frames`.
-/

namespace Nanodregg.Protocol

open Nanodregg.Codec

/-- A step as it travels: its tag, then that step's fields. -/
abbrev Step.Frame := (s : Step) × Layout.Ty Bounds.frameBytesMax s.layout

def Step.frame : Stream Step.Frame :=
  Stream.tagged Step.all Step.code Step.ofCode? fun s => Layout.codec Bounds.frameBytesMax (by decide) s.layout

/-- The argv layout, its items and count bounded by `argvBytesMax`, and the whole payload too:
a payload over `argvBytesMax` bytes is refused as `pastBound` (CLIENT-2: the total is Lean's). -/
def commandFrame :
    Stream { v : Layout.Ty Bounds.argvBytesMax commandLayout //
      (Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size v ≤ Bounds.argvBytesMax } :=
  Stream.within Bounds.argvBytesMax (Layout.codec Bounds.argvBytesMax (by decide) commandLayout)

/-- A frame BODY the transport carries: its op or status byte and `payload`, at most `frameBytesMax`
bytes AS A WHOLE (`Host.Wire.bodyMax`'s reader, `client/src/frame.rs`'s `read_body`/`write_body`).
A layout bounds each field by the frame on its own; this is the bound on their sum (PROTOCOL-70). -/
def bodyFits (payload : ByteArray) : Bool := decide (1 + payload.size ≤ Bounds.frameBytesMax)

def resumeFrame : Stream (Layout.Ty Bounds.frameBytesMax resumeLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) resumeLayout

def signResultFrame : Stream (Layout.Ty Bounds.frameBytesMax signResultLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) signResultLayout

def precommitResultFrame : Stream (Layout.Ty Bounds.frameBytesMax precommitResultLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) precommitResultLayout

def envelopeFrame : Stream (Layout.Ty Bounds.frameBytesMax envelopeLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) envelopeLayout

def logReplyFrame : Stream (Layout.Ty Bounds.frameBytesMax logReplyLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) logReplyLayout

def custodyRefusalFrame : Stream (Layout.Ty Bounds.frameBytesMax custodyRefusalLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) custodyRefusalLayout

def expiredRefusalFrame : Stream (Layout.Ty Bounds.frameBytesMax expiredRefusalLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) expiredRefusalLayout

def readReplyFrame : Stream (Layout.Ty Bounds.frameBytesMax readReplyLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) readReplyLayout

/-! ## The frames themselves, and the client's one durable record (CLIENT-40)

The socket frame and the child wire's are `Stream.bytesOf` of their body, and what a body says is
`bodyParts?` / `Host.Wire.decodeBody`. `client/src/frame.rs` and `client/src/mux.rs` read and write
them by hand over a deadline; `gates/codec-vectors.tsv` pins Lean's verdict on each site's bytes and
`client/tests/vectors.rs` decodes the same bytes in Rust, renders the same text and re-encodes. -/

/-- A frame on either client socket, either direction: `u32le len ‖ body`, `len ≤ frameBytesMax`. -/
def socketFrame : Stream (Bytes Bounds.frameBytesMax) := Stream.bytesOf Bounds.frameBytesMax

/-- What a socket frame's body says: its first byte (a request's op, a reply's status) and the rest. An
empty body carries no op byte and says nothing: the client refuses it `empty`. -/
def bodyParts? (b : ByteArray) : Option (UInt8 × ByteArray) :=
  if h : 0 < b.size then some (b[0], b.extract 1 b.size) else none

/-- The armed rotation record (`ws/rotation`): `rotationLayout` with each key at most
`Ed25519.publicKeyBytes` bytes. -/
def rotationFrame : Stream (Layout.Ty Ed25519.publicKeyBytes rotationLayout) :=
  Layout.codec Ed25519.publicKeyBytes (by decide) rotationLayout

/-- The record's size when both keys are whole public keys: the only size the client reads
(`rotationFrame_size`). -/
def rotationBytes : Nat := Stream.u64.size 0 + 2 * (Stream.u32.size 0 + Ed25519.publicKeyBytes)

end Nanodregg.Protocol
