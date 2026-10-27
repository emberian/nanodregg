/-
# Protocol.Certified — the stranger's check: a World's head from its genesis input and a certificate (PROTOCOL-78; DESIGN-TRUST T3e)

A STRANGER holds no Store, no member key and no invitation: only a World's genesis input (the bytes
`host genesis` prints as `input`, the one start encoding `Invite.startOf` reads) and a certificate
(`base.cert`, or one a member forwards). The input commits the World's authority in its origin
(KERNEL-69: `originOf` hashes it), so the stranger needs no one's word for whom to trust: it decodes
the input, makes its genesis (`Receive.genesis`: the inputs checked, refused by name), and takes the
head the certificate certifies under THAT authority for THAT origin (`Head.certified`). Nothing else
is asked: what a stranger learns is exactly `Proofs.Certified.stranger_ok` — the head is certified by
`threshold` distinct certifiers the genesis lists, for the World the input makes.

A carried start (PROTOCOL-85) is the carry start its origin is the digest of, the stated authority in
it (KERNEL-79): the stranger checks the authority by genesis's own `checkAuthority`, recomputes the
origin (`carryOriginOfStart`) and takes the head the certificate certifies under that authority, as
for a genesis. The carried World's certificates are its own: none of the World it was carried from
names its origin (`otherWorld`).
-/
import Protocol.Head
import Protocol.Invite

namespace Nanodregg.Protocol.Certified

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol.Head

variable {D : Type} [Ord D] [DecidableEq D]

/-- Why a stranger takes no head (law 7). -/
inductive Refusal
  /-- the input bytes are not one start encoding -/
  | badInput
  /-- the inputs make no World (`Receive.genesis`'s refusal, by its name) -/
  | inputs (r : GenesisRefusal)
  /-- the certificate does not certify a head of that World under its authority (`Head.certified`) -/
  | cert (r : CertRefusal)

def Refusal.name : Refusal → String
  | .badInput => "badInput" | .inputs r => r.name | .cert r => r.name

/-- THE stranger's check. -/
def check (X : Ctx D) (input cert : ByteArray) : Except Refusal (Head D) :=
  match Invite.startOf X input with
  | none => .error .badInput
  | some (.carried s _) =>
    match checkAuthority s.auth with
    | .error r => .error (.inputs r)
    | .ok () =>
      match certified X s.auth (carryOriginOfStart X s) cert with
      | .error r => .error (.cert r)
      | .ok c => .ok c.head
  | some (.genesis name nonce allowance fs auth) =>
    match genesis X name nonce allowance fs auth with
    | .error r => .error (.inputs r)
    | .ok w =>
      match certified X auth w.origin cert with
      | .error r => .error (.cert r)
      | .ok c => .ok c.head

end Nanodregg.Protocol.Certified
