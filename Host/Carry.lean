/-
# Host.Carry — the carried file of `host export` / `host import` (HOST-28)

    OUT = stamp32 ‖ head ‖ carried
    head    = from ‖ u64 height ‖ chain        (`Carry.head dc`: the exported World's origin and
                                                the anchor it was taken at)
    carried = CODEC's `Codec.Kernel.carried`   (KERNEL's `World.carried`: trie, allowance, height,
                                                the journal inside its window)

`stamp32` is the digest of the codec tags of `head` and `carried` (`Carry.stamp`), the D2
discipline applied to the export: a file written under other shapes is refused `shapeMismatch`
by name, before a byte of it is decoded, never reinterpreted. Nobody promises the carried shape
stable (HOST-28): a flag day that changes it cannot carry.

The file is not MAC'd (no Store key crosses a flag day, HOST-16). `export` prints the file's
digest (`Carry.digestOf`, its own domain) and `import --digest` is REQUIRED: the operator's
out-of-band link from the old Store to the bytes imported. `Carry.read` checks, in order and
before anything is written: the digest (`digest`), the stamp (`shapeMismatch`), the head and the
carried bytes decode (`decode`), and the head's height is the carried height (`anchor`). Import
then builds the World by KERNEL's ONE carry (`Receive.carry`) and writes it with the one genesis
(`Host.genesis`); the reopen's carried bytes must be the file's (`reopen`). Every refusal but
`shapeMismatch` and the kernel's own is `carryMismatch` with its reason on stderr.

Export checks its own file reads back (`Carry.exportFile`) before it writes OUT.
Theorems: `Host.Proofs.Carry`.
-/
import Kernel.Receive.Follow
import Codec.World
import Codec.Tag
import Codec.Hash
import Codec.Raw
import Host.Exit

namespace Nanodregg.Host.Carry

open Nanodregg.Kernel Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-- The head of a carried file: the exported World's origin, and the anchor (height, chain). -/
structure Head (D : Type) where
  fromOrigin : D
  height : Nat
  chain : D

def head (dc : Stream D) : Stream (Head D) :=
  Stream.refine "host/carried-head" (Stream.product dc (Stream.product Stream.nat64 dc))
    (fun (o, h, c) => some ⟨o, h, c⟩) (fun x => (x.fromOrigin, x.height, x.chain))

def domStamp : String := "nanodregg/host/carried/v1"

/-- The file's digest domain: the digest `export` prints and `import --digest` requires. -/
def domFile : String := "nanodregg/host/carried-file/v1"

/-- The stamp of a carried file: the digest of the head's and the carried codec's tags. Computed
from the codecs, never written as a literal. -/
def stamp (E : Env D) (dc : Stream D) : Digest :=
  Hash.digest domStamp ((Tag.of "host/carried-head" (head dc)).bytes ++
    (Tag.of "host/carried" (Codec.Kernel.carried E dc)).bytes)

def stampBytes : Nat := 32

def digestOf (f : ByteArray) : Digest := Hash.digest domFile f

/-- The carried file of `w`. -/
def file (E : Env D) (dc : Stream D) (w : World D) : ByteArray :=
  (stamp E dc).bytes ++ (head dc).bytes ⟨w.origin, w.height, w.chain⟩ ++
    (Codec.Kernel.carried E dc).bytes w.carried

/-- Why a carried file is not imported (or exported). -/
inductive Fault where
  /-- the file does not hash to the digest the operator gave -/
  | digest
  /-- the file was written under other shapes (`stored`) than this binary's -/
  | stamp (stored : ByteArray)
  /-- the head or the carried bytes do not decode -/
  | decode (r : Refusal)
  /-- the head's anchor height is not the carried height -/
  | anchor
  /-- the imported Store reopened to other carried bytes than the file's -/
  | reopen
  /-- the exported file does not read back to the exported World's carried bytes -/
  | exportCheck
  deriving Repr

def Fault.name : Fault → String
  | .digest => "digest"
  | .stamp _ => "shapeMismatch"
  | .decode _ => "decode"
  | .anchor => "anchor"
  | .reopen => "reopen"
  | .exportCheck => "export"

/-- A file read back: its head and carried state, and where the carried bytes start. -/
structure Read (D : Type) [Ord D] where
  head : Head D
  carried : Carried D
  carriedAt : Nat

/-- Read a carried file, checking (in this order, before anything is written) its digest, its
stamp, that its head and carried bytes decode, and that the anchor height is the carried one. -/
def read (E : Env D) (dc : Stream D) (want : Digest) (f : ByteArray) : Except Fault (Read D) :=
  if digestOf f ≠ want then .error .digest else
  if f.extract 0 stampBytes ≠ (stamp E dc).bytes then .error (.stamp (f.extract 0 stampBytes)) else
  match (head dc).get f stampBytes with
  | .error r => .error (.decode r)
  | .ok (h, j) =>
    match (Codec.Kernel.carried E dc).decode (f.extract j f.size) with
    | .error r => .error (.decode r)
    | .ok c => if h.height ≠ c.height then .error .anchor else .ok ⟨h, c, j⟩

/-- The World an import makes from a file read back: KERNEL's one carry, under the new name and
nonce, from the exported origin. -/
def world (X : Receive.Ctx D) (name nonce : ByteArray) (r : Read D) : Except Receive.CarryRefusal (World D) :=
  Receive.carry X name nonce r.head.fromOrigin r.carried

/-- THE import decision, pure (`host import` and PROTOCOL's carry row both call it): read the file
under the operator's digest, then KERNEL's one carry. A refusal is its exit Status and its stderr
name: another stamp is `shapeMismatch`; a name or nonce past its bound `usage`; anything else
`carryMismatch` with its reason. -/
def importWorld (X : Receive.Ctx D) (dc : Stream D) (name nonce : ByteArray) (want : Digest)
    (f : ByteArray) : Except (Status × String) (World D × Read D) :=
  match read X.env dc want f with
  | .error (.stamp _) => .error (.shapeMismatch, "carried")
  | .error e => .error (.carryMismatch, s!"carryMismatch {e.name}")
  | .ok r =>
    match world X name nonce r with
    | .ok w => .ok (w, r)
    | .error .nameTooLong => .error (.usage, "nameTooLong")
    | .error .nonceTooLong => .error (.usage, "nonceTooLong")
    | .error e => .error (.carryMismatch, s!"carryMismatch carry {e.name}")

/-- Export's own check of a file `f` for `w`: it reads back, under its own digest, to `w`'s carried
bytes and to `w`'s head (origin, height, chain); otherwise `exportCheck`, and nothing is written. -/
def exportCheck (E : Env D) (dc : Stream D) (w : World D) (f : ByteArray) : Except Fault ByteArray :=
  match read E dc (digestOf f) f with
  | .error _ => .error .exportCheck
  | .ok r =>
    if (Codec.Kernel.carried E dc).bytes r.carried = (Codec.Kernel.carried E dc).bytes w.carried ∧
        r.head.fromOrigin = w.origin ∧ r.head.height = w.height ∧ r.head.chain = w.chain then .ok f
    else .error .exportCheck

/-- The file `export` writes for `w`, checked. -/
def exportFile (E : Env D) (dc : Stream D) (w : World D) : Except Fault ByteArray :=
  exportCheck E dc w (file E dc w)

end Nanodregg.Host.Carry
