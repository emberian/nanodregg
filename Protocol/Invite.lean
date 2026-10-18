/-
# Protocol.Invite — an invitation: the World a joiner derives itself, vouched for by its sponsor

A member's `Self.world` is its own Store's genesis origin (KERNEL-24), and that genesis is built from
the World's ORIGIN INPUTS: the name, HOST's nonce, the allowance and the founders (`Receive.genesisInput`).
Before PROTOCOL-42 a joiner learned those inputs from whoever handed them over: trust on first use,
which binds it to the first bytes it sees, a hostile Host's included (ASSEMBLY D1's critique).

An invitation is those inputs plus the sponsor's PIN of its own World (its step count and the digest
of its World bytes, `Thin.Pin`), the sponsor's member id as the sponsor states it (the id `init`
names; signed, never checked against the World: a full joiner learns it is a member when its
`enroll` lands) and key, all signed by
that key under `domInvite`. The joiner names the sponsor key it trusts (out of band: a person's word)
and `accept` decides: the bytes decode, the signer is the trusted key, the signature verifies over
exactly the bytes carried, and the inputs make a genesis. The World the joiner then folds from is
`Receive.genesis` of the signed inputs (`Proofs.Invite.accept_ok`); its origin is computed, never
read. A thin joiner adopts the pinned base (`adopt INVITE KEY`, the same `accept`), so a pin is no
longer a 32-byte digest carried by an unbuilt channel: it is signed by the trusted key.
-/
import Kernel.Receive.Follow
import Protocol.Thin
import Protocol.Command.Text

namespace Nanodregg.Protocol.Invite

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- The domain every invitation message begins with (pairwise disjoint from the other signed shapes:
`Protocol.Proofs.Domains`). -/
def domInvite : ByteArray := "nanodregg/protocol/invitation/v1".toUTF8

/-- The signed part: the origin inputs (`genesisInput`'s bytes), the pin's step count and digest,
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

/-- A decoded invitation. `founders` carries each founder's next-key DIGEST, as `Receive.genesis`
takes it. -/
structure Invitation (D : Type) where
  name : ByteArray
  nonce : ByteArray
  allowance : Nat
  founders : List (ByteArray × D)
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
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .badInvitation => "badInvitation" | .notSponsor => "notSponsor" | .pinMismatch => "pinMismatch"
  | .inputs r => r.name | .otherWorld => "otherWorld" | .noBase => "noBase"
  | .baseMismatch => "baseMismatch"

/-- The constructor's index, the thing a name must determine (`Proofs.Invite.Refusal.name_injective`). -/
def Refusal.tag : Refusal → Nat
  | .badInvitation => 0 | .notSponsor => 1 | .pinMismatch => 2 | .inputs _ => 3 | .otherWorld => 4 | .noBase => 5
  | .baseMismatch => 6

/-- The founders with their next-key digests decoded, or `none` if one is not a digest. -/
def foundersOf (X : Ctx D) : List (ByteArray × ByteArray) → Option (List (ByteArray × D))
  | [] => some []
  | (k, n) :: rest => do pure ((k, ← X.digestOf n) :: (← foundersOf X rest))

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
  genesisInput.bytes (inputOf X name nonce allowance founders)

/-- What the signed bytes say, decoded: the inputs (founders' next-key digests decoded), the pin,
the sponsor and its key. -/
structure Said (D : Type) where
  name : ByteArray
  nonce : ByteArray
  allowance : Nat
  founders : List (ByteArray × D)
  pin : Thin.Pin
  sponsor : D
  key : ByteArray

/-- Decode the signed bytes, checking nothing they state. -/
def said (X : Ctx D) (u : ByteArray) : Option (Said D) :=
  match unsignedFrame.decode u with
  | .error _ => none
  | .ok (i, st, d, sp, k, ()) =>
    match genesisInput.decode i.1 with
    | .error _ => none
    | .ok (name, nonce, allowance, fs) => do
      pure { name, nonce, allowance, founders := ← foundersOf X fs, pin := ⟨st.toNat, d.1⟩,
             sponsor := ← X.digestOf sp.1, key := k.1 }

/-- Decode an invitation, checking nothing it states. -/
def ofBytes (X : Ctx D) (b : ByteArray) : Option (Invitation D) :=
  match invitationFrame.decode b with
  | .error _ => none
  | .ok (u, s, ()) => do
    let v ← said X u.1
    pure { name := v.name, nonce := v.nonce, allowance := v.allowance, founders := v.founders,
           pin := v.pin, sponsor := v.sponsor, key := v.key, unsigned := u.1, signature := s.1 }

/-- THE decision a joiner makes about an invitation, given the sponsor key it trusts: decoded, signed
by that key, the signature good over the bytes carried, and the inputs a genesis. The World returned
is the genesis the joiner's own Store starts from; its origin is the member's `Self.world`. -/
def accept (X : Ctx D) (trusted bytes : ByteArray) : Except Refusal (Invitation D × World D) := do
  let some inv := ofBytes X bytes | throw .badInvitation
  if inv.key ≠ trusted then throw .notSponsor
  if !X.verify inv.key (message inv.unsigned) inv.signature then throw .pinMismatch
  match genesis X inv.name inv.nonce inv.allowance inv.founders with
  | .error r => throw (.inputs r)
  | .ok w => pure (inv, w)

end Nanodregg.Protocol.Invite
