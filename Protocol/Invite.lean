/-
# Protocol.Invite — the sponsor-signed start and checkpoint pin

Start is genesis (name, nonce, allowance, founders) or carried (new origin, name, nonce,
exported origin, height, chain). One tagged startInput encoding is signed with the checkpoint
pin, sponsor id and key under domInvite. accept is genesis-only; acceptStart verifies either
start and returns the origin the joiner must pin. A carried join obtains the export separately
and reconstructs it under that signed name, nonce and origin (Host.Cli.joinWith).
-/
import Kernel.Receive.Follow
import Protocol.Thin
import Protocol.Command.Text

namespace Nanodregg.Protocol.Invite

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- The domain every invitation message begins with (pairwise disjoint from the other signed shapes:
`Protocol.Proofs.Domains`). -/
def domInvite : ByteArray := "nanodregg/protocol/invitation/v2".toUTF8

/-- The signed part: the startInput bytes, the pin's step count and digest,
the sponsor's member id bytes and its key. -/
def unsignedLayout : Layout :=
  [.bytes "input", .u64 "steps", .bytes "digest", .bytes "sponsor", .bytes "key"]

/-- An invitation on the wire: the signed bytes as carried, then the signature over them. -/
def invitationLayout : Layout := [.bytes "unsigned", .bytes "signature"]

def unsignedFrame : Stream (Layout.Ty Bounds.frameBytesMax unsignedLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) unsignedLayout

def invitationFrame : Stream (Layout.Ty Bounds.frameBytesMax invitationLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) invitationLayout

variable {D : Type} [Ord D] [DecidableEq D]

/-- The signed start: a genesis, or a carried World pinned by its new origin. -/
inductive Start (D : Type) where
  | genesis (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
  | carried (origin : D) (name nonce : ByteArray) (fromOrigin : D) (height : Nat) (chain : D)

/-- The carry start's wire fields. Digests use the same raw byte encoding as genesis inputs. -/
abbrev CarriedStart := ByteArray × ByteArray × ByteArray × ByteArray × Nat × ByteArray

open Stream in
def carriedStart : Stream CarriedStart :=
  product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax)
    (product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax)
      (product nat64 (rawBytes Bounds.eventBytesMax)))))

def startInput : Stream (GenesisInput ⊕ CarriedStart) := Stream.sum genesisInput carriedStart

def startBytes (X : Ctx D) : Start D → ByteArray
  | .genesis name nonce allowance fs => startInput.bytes (.inl (inputOf X name nonce allowance fs))
  | .carried o name nonce fromO height chain =>
    startInput.bytes (.inr (X.env.bytes o, name, nonce, X.env.bytes fromO, height, X.env.bytes chain))

/-- A decoded invitation. -/
structure Invitation (D : Type) where
  start : Start D
  pin : Thin.Pin
  sponsor : D
  key : ByteArray
  /-- the signed bytes exactly as carried (`unsignedFrame`) -/
  unsigned : ByteArray
  signature : ByteArray

/-- What the sponsor signs. -/
def message (unsigned : ByteArray) : ByteArray := domInvite ++ unsigned

/-- Why an invitation is not accepted (law 7). -/
inductive Refusal
  /-- the bytes are not an invitation (either frame, the inputs, a digest) -/
  | badInvitation
  /-- signed by another key than the one the joiner trusts -/
  | notSponsor
  /-- the signature does not verify over the bytes carried: an input (a forged origin), the pin or
  the sponsor was changed after the sponsor signed, or the signature itself -/
  | pinMismatch
  /-- the signed inputs make no genesis (`GenesisRefusal`, by its own name) -/
  | inputs (r : GenesisRefusal)
  /-- the inputs make another World than the member's own (`invite`), or the invitation is to
  another World (`adopt`); named apart from the envelope's and thin's `wrongWorld` -/
  | otherWorld
  /-- `invite`: follow never sat at the writer's newest base, so it has no digest of its own to pin
  (none since it started, or only an older base); `host seal STORE` then a catch-up gives one -/
  | noBase
  /-- `invite`: the writer states a base digest that is not follow's own World at that step count -/
  | baseMismatch
  | carried
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .badInvitation => "badInvitation" | .notSponsor => "notSponsor" | .pinMismatch => "pinMismatch"
  | .inputs r => r.name | .otherWorld => "otherWorld" | .noBase => "noBase"
  | .baseMismatch => "baseMismatch" | .carried => "carriedWorld"

/-- The constructor's index, the thing a name must determine (`Proofs.Invite.Refusal.name_injective`). -/
def Refusal.tag : Refusal → Nat
  | .badInvitation => 0 | .notSponsor => 1 | .pinMismatch => 2 | .inputs _ => 3 | .otherWorld => 4 | .noBase => 5
  | .baseMismatch => 6 | .carried => 7

/-- The founders with their next-key digests decoded, or `none` if one is not a digest. -/
def foundersOf (X : Ctx D) : List (ByteArray × ByteArray) → Option (List (ByteArray × D))
  | [] => some []
  | (k, n) :: rest => do pure ((k, ← X.digestOf n) :: (← foundersOf X rest))

/-- Decode the one start encoding, including every carried digest. -/
def startOf (X : Ctx D) (b : ByteArray) : Option (Start D) := do
  let .ok raw := startInput.decode b | none
  match raw with
  | .inl (name, nonce, allowance, fs) =>
    pure (.genesis name nonce allowance (← foundersOf X fs))
  | .inr (o, name, nonce, fromO, height, chain) =>
    pure (.carried (← X.digestOf o) name nonce (← X.digestOf fromO) height (← X.digestOf chain))

/-- The genesis-only admission; carried starts require a separately supplied export. -/
def startGenesis (X : Ctx D) : Start D → Except Refusal (World D)
  | .genesis name nonce allowance fs => (genesis X name nonce allowance fs).mapError .inputs
  | .carried .. => .error .carried

/-- The origin to which the signed start commits. Genesis inputs are checked before returning it. -/
def startOrigin (X : Ctx D) : Start D → Except Refusal D
  | .genesis name nonce allowance fs => do
    let w ← (genesis X name nonce allowance fs).mapError .inputs
    pure w.origin
  | .carried o .. => .ok o

/-- The unsigned bytes of an invitation's fields, or `none` past the frame bound. -/
def unsignedBytes (X : Ctx D) (input : ByteArray) (pin : Thin.Pin) (sponsor : D) (key : ByteArray) :
    Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (unsignedFrame.bytes (← f input, pin.steps.toUInt64, ← f pin.digest, ← f (X.env.bytes sponsor),
    ← f key, ()))

/-- An invitation's wire bytes, or `none` past the frame bound. -/
def bytes (unsigned signature : ByteArray) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (invitationFrame.bytes (← f unsigned, ← f signature, ()))

/-- The input bytes of a genesis (what `host genesis` prints and a founder invites from). -/
def inputBytes (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    ByteArray :=
  startBytes X (.genesis name nonce allowance founders)

/-- What the signed bytes say, decoded: the inputs (founders' next-key digests decoded), the pin,
the sponsor and its key. -/
structure Said (D : Type) where
  start : Start D
  pin : Thin.Pin
  sponsor : D
  key : ByteArray

/-- Decode the signed bytes, checking nothing they state. -/
def said (X : Ctx D) (u : ByteArray) : Option (Said D) :=
  match unsignedFrame.decode u with
  | .error _ => none
  | .ok (i, st, d, sp, k, ()) =>
    do pure { start := ← startOf X i.1, pin := ⟨st.toNat, d.1⟩,
              sponsor := ← X.digestOf sp.1, key := k.1 }

/-- Decode an invitation, checking nothing it states. -/
def ofBytes (X : Ctx D) (b : ByteArray) : Option (Invitation D) :=
  match invitationFrame.decode b with
  | .error _ => none
  | .ok (u, s, ()) => do
    let v ← said X u.1
    pure { start := v.start,
           pin := v.pin, sponsor := v.sponsor, key := v.key, unsigned := u.1, signature := s.1 }

/-- Signature admission shared by both kinds of start. -/
def verified (X : Ctx D) (trusted bytes : ByteArray) : Except Refusal (Invitation D) := do
  let some inv := ofBytes X bytes | throw .badInvitation
  if inv.key ≠ trusted then throw .notSponsor
  if !X.verify inv.key (message inv.unsigned) inv.signature then throw .pinMismatch
  pure inv

/-- Genesis-only admission. A carried invitation is refused by name. -/
def accept (X : Ctx D) (trusted bytes : ByteArray) : Except Refusal (Invitation D × World D) := do
  let inv ← verified X trusted bytes
  let w ← startGenesis X inv.start
  pure (inv, w)

/-- The signed invitation and its independently pinned origin, for either kind of start. -/
def acceptStart (X : Ctx D) (trusted bytes : ByteArray) : Except Refusal (Invitation D × D) := do
  let inv ← verified X trusted bytes
  let o ← startOrigin X inv.start
  pure (inv, o)

end Nanodregg.Protocol.Invite
