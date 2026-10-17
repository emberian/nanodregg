/-
# Protocol.Thin — a member that starts from a pinned base, not from genesis (PROTOCOL-14, option A)

A thin member holds a PIN: a height and the digest of the World bytes at that height
(`Host.Keys.worldDigest`, deployed `Hash.digest "nanodregg/host/base-digest/v1"`, unkeyed, HOST-15), which
it trusts out of
band: its own earlier fold, or a full follower's word (that channel is Ember's, unbuilt). It pages
the writer's newest base with `read` (`readReplyLayout`) and `accept` decides each page. It trusts
NOTHING the page states: the assembled bytes are adopted only if they hash to the pin and decode to
a World at the pinned height (`Protocol.Proofs.Thin.accept_done`). A forged byte anywhere in the
served base is `baseMismatch`. From the adopted World on, the member is an ordinary follower: the
same catch-up re-derives every event after the base (PROTOCOL-4), so consent is full from the pin
on; what it trusts is the history before it.

The pin binds the World's every byte, so its height AND its chain (both in the World bytes): the
decoded World's height is checked against the pin's, and its chain is what the next `log` page
must continue (`chainMismatch` otherwise). Bytes are checked against the pin BEFORE they are decoded: undecodable bytes that hash to the pin
are the pin's fault (`baseUndecodable`), never a guess about the writer.
-/
import Protocol.Frames
import Protocol.Command.Text

namespace Nanodregg.Protocol.Thin

/-- What a thin member trusts: the World at `height` has World bytes hashing to `digest`. -/
structure Pin where
  height : Nat
  digest : ByteArray
  deriving DecidableEq

/-- How a base is read: the World codec, a World's height, the digest of World bytes a pin names
(the writer's `Keys.worldDigest`: deployed, HOST-15's cSHAKE256; the Sim's, a toy), and the bound
on a World's bytes. -/
structure Base (W : Type) where
  world : Codec.Stream W
  heightOf : W → Nat
  digest : ByteArray → ByteArray
  bytesMax : Nat

/-- A base download in progress: the bytes `[0, got.size)` of a base `total` bytes long. It lives
in follow's memory only; a restarted follow starts the download again. -/
structure Download where
  pin : Pin
  total : Nat
  got : ByteArray

/-- One `read` page, as decoded (`readReplyLayout`). -/
structure Page where
  height : Nat
  total : Nat
  digest : ByteArray
  chain : ByteArray
  bytes : ByteArray

def Page.ofBytes (b : ByteArray) : Option Page :=
  match readReplyFrame.decode b with
  | .ok (h, t, d, c, x, ()) => do
      pure { height := ← Text.ofU64 h.1, total := ← Text.ofU64 t.1, digest := d.1, chain := c.1,
             bytes := x.1 }
  | .error _ => none

/-- A page's wire bytes, or `none` when a field does not fit a frame. -/
def Page.toBytes (p : Page) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (readReplyFrame.bytes (← f (Text.u64 p.height), ← f (Text.u64 p.total), ← f p.digest,
    ← f p.chain, ← f p.bytes, ()))

/-- Why a base is not adopted (law 7). -/
inductive Refusal
  /-- the `read` reply does not decode as a page -/
  | badPage
  /-- the writer's newest base is at another height than the pin: a newer seal (get a fresh pin)
  or a writer serving an older one -/
  | baseMoved (height : Nat)
  /-- the page states another digest, or the assembled bytes do not hash to the pin, or they
  decode to a World at another height: a forged or corrupted base -/
  | baseMismatch
  /-- a page that does not continue the download: another total, no bytes, or past the total -/
  | pageMismatch
  /-- the stated total is past the bound on a World's bytes -/
  | baseTooLarge (total : Nat)
  /-- bytes that hash to the pin do not decode as a World: the pin itself names no World -/
  | baseUndecodable
  /-- follow's World is already at or past the pin: nothing to adopt -/
  | notBehind (height : Nat)
  /-- follow's own Store already holds Turns past genesis: an adopted base over them would leave
  two histories in one Store, follow's own up to `height` and the writer's from the pin, with the
  heights between in neither (HOST-3's review; law 1). A thin member adopts from a fresh Store. -/
  | notAtGenesis (height : Nat)
  /-- the command read its page budget; the download is kept and the member runs it again -/
  | incomplete (got total : Nat)
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .badPage => "badPage" | .baseMoved _ => "baseMoved" | .baseMismatch => "baseMismatch"
  | .pageMismatch => "pageMismatch" | .baseTooLarge _ => "baseTooLarge"
  | .baseUndecodable => "baseUndecodable" | .notBehind _ => "notBehind" | .incomplete _ _ => "incomplete"
  | .notAtGenesis _ => "notAtGenesis"

def Refusal.tag : Refusal → Nat
  | .badPage => 0 | .baseMoved _ => 1 | .baseMismatch => 2 | .pageMismatch => 3
  | .baseTooLarge _ => 4 | .baseUndecodable => 5 | .notBehind _ => 6 | .incomplete _ _ => 7 | .notAtGenesis _ => 8

/-- The download held for `pin`, if any (a download for another pin is dropped). -/
def held (pin : Pin) : Option Download → Option Download
  | some d => if d.pin = pin then some d else none
  | none => none

/-- The byte offset the next page is asked from. -/
def offset (pin : Pin) (dl : Option Download) : Nat :=
  ((held pin dl).map (·.got.size)).getD 0

/-- What one page leads to. -/
inductive Progress (W : Type)
  /-- more bytes to fetch, from `got.size` -/
  | more (d : Download)
  /-- the base, adopted -/
  | done (w : W)

variable {W : Type}

/-- The download held for `pin` was of another total: not a continuation. -/
def totalMoved (pin : Pin) (dl : Option Download) (total : Nat) : Bool :=
  match held pin dl with
  | some d => d.total != total
  | none => false

/-- The last check of a download: the bytes hash to the pin, then decode to a World at the pinned
height. -/
def finish (B : Base W) (pin : Pin) (got : ByteArray) : Except Refusal (Progress W) :=
  if B.digest got ≠ pin.digest then .error .baseMismatch else
  match B.world.decode got with
  | .error _ => .error .baseUndecodable
  | .ok w => if B.heightOf w ≠ pin.height then .error .baseMismatch else .ok (.done w)

/-- Decide one page of the base download for `pin`, given the download so far. -/
def accept (B : Base W) (pin : Pin) (dl : Option Download) (p : Page) : Except Refusal (Progress W) :=
  let got := ((held pin dl).map (·.got)).getD ByteArray.empty
  if p.height ≠ pin.height then .error (.baseMoved p.height)
  else if p.digest ≠ pin.digest then .error .baseMismatch
  else if B.bytesMax < p.total then .error (.baseTooLarge p.total)
  else if totalMoved pin dl p.total then .error .pageMismatch
  else if p.bytes.size = 0 ∨ p.total < got.size + p.bytes.size then .error .pageMismatch
  else if (got ++ p.bytes).size < p.total then .ok (.more ⟨pin, p.total, got ++ p.bytes⟩)
  else finish B pin (got ++ p.bytes)

end Nanodregg.Protocol.Thin
