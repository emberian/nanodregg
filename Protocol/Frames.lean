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

def readReplyFrame : Stream (Layout.Ty Bounds.frameBytesMax readReplyLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) readReplyLayout

end Nanodregg.Protocol
