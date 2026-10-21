/-
Physical segment identities (HOST-71). Logical offsets stay u64. A generation is
selected only by the atomically installed base; files in another generation are invisible.
The wrappers authenticate the identity together with the complete logical header/base.
-/
import Host.Segment

namespace Nanodregg.Host
open Nanodregg.Codec

def segmentIdentity (generation offset : Nat) : Nat := generation * 2 ^ 64 + offset

def physicalBytes : Nat := 40

def physicalPack (keys : Keys) (kind : String) (generation : Nat) (logical : ByteArray) : ByteArray :=
  let body := logical ++ Stream.nat64.bytes generation
  body ++ keys.checkpoint.tag (kind.toUTF8 ++ body)

def physicalRead (keys : Keys) (kind : String) (bytes : ByteArray) : Option (Nat × ByteArray) := do
  if bytes.size < physicalBytes then none else do
  let body := bytes.extract 0 (bytes.size - Log.tagBytes)
  let tag := bytes.extract (bytes.size - Log.tagBytes) bytes.size
  if keys.checkpoint.tag (kind.toUTF8 ++ body) ≠ tag then none else do
  let generation ← (Stream.nat64.decode (body.extract (body.size - 8) body.size)).toOption
  return (generation, body.extract 0 (body.size - 8))

def physicalHeaderBytes (keys : Keys) : Nat := headerBytes keys + physicalBytes

def physicalHeader (keys : Keys) (generation : Nat) (h : Header) : ByteArray :=
  physicalPack keys "header-identity" generation (Header.bytes keys h)

/-- Authenticate the logical frame and check its stamp BEFORE decoding the identity trailer
or the World. Thus a pre-HOST-71 base refuses shapeMismatch, not a missing identity file. -/
def physicalBaseRead (keys : Keys) (c : Cadence) (bytes : ByteArray) :
    Except BaseFault (Nat × ByteArray) :=
  match Log.frameAt keys.base c.baseRecordMax bytes 0 baseInitial with
  | none => .error .baseCorrupt
  | some r =>
    let stored := r.record.extract 0 stampBytes
    if stored ≠ keys.shapes.bytes then .error (.shapeMismatch stored.data keys.shapes.bytes.data)
    else match physicalRead keys "base-identity" bytes with
      | none => .error .baseCorrupt
      | some (g, file) =>
        if r.next = file.size then .ok (g, file) else .error .baseCorrupt

/-- The physical header reader used by Store.readHeader: authentication and logical
decode precede the check against the selected generation and requested logical start. -/
def physicalHeaderRead (keys : Keys) (generation offset : Nat) (bytes : ByteArray) :
    Except BaseFault (Header × ByteArray) :=
  match physicalRead keys "header-identity" bytes with
  | none => .error .checkpointCorrupt
  | some (g, logical) =>
    match Header.read keys logical with
    | none => .error .checkpointCorrupt
    | some h =>
      if g = generation ∧ h.start = offset then .ok (h, logical)
      else .error .foreignSegment

/-- Strictly above every generation represented in the directory, including crash orphans.
The IO allocator bounds this result to u64 before encoding it. -/
def nextGeneration : List Nat → Nat
  | [] => 0
  | id :: ids => max (id / 2 ^ 64 + 1) (nextGeneration ids)

/-- A live reader uses this unauthenticated footer ONLY to refuse a moved base.
It never accepts a new World or switches the logical reader from this metadata. -/
def generationFault (expected : Nat) (bytes : ByteArray) : Option BaseFault :=
  match Stream.nat64.decode bytes with
  | .error _ => some .baseCorrupt
  | .ok generation => if generation = expected then none else some .foreignSegment

end Nanodregg.Host
