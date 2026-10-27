/-
# Hosting.Certify — what the writer's certify key may sign (HOSTING-56; DESIGN-TRUST §4.4b)

The writer's signing seed is not in the writer: it sits in keybroker's key file (slot `certify`),
and keybroker signs with it only what this decision grants. The writer asks on its own socket with
the certified bytes of a head (`Protocol.Head.certifiedLayout`); the decider (`hosting-broker`,
which already follows the Store as a `Host.Tail` for the allowances) grants exactly the bytes of a
head ITS OWN fold produced at a record end, and keybroker signs `domCertify ‖ bytes` with the slot.

A `Certifier` is that fold's view: the World's origin, the heads at the last `headsMax` record ends
the decider absorbed (ascending; the tip last), the last head it certified, and whether the Store it
opened is tied to that head (`anchored`). A grant (`decide`) is:

- the bytes read back as a head byte for byte (`badCertify`), of THIS World (`notOnFold`);
- the decider is anchored (`unanchored`): the head it last certified lies on the fold it now holds;
- the head is not below the last certified one, and at its step count IS it (`regressed`): so the
  heads granted over every decider life form one chain of step counts with one head per count
  (`Proofs.Certify.granted_one_head`), whatever the Store's files say after a restart, as long as
  the last certified head survives the restart (keybroker persists it beside KEYS before it signs);
- the step count is not past the decider's tip (`notYet`: the writer asks again), and the head is
  one the fold holds (`notOnFold`).

ANCHORING. Within one decider life every head comes from one fold, so each extends the one before.
Across a restart the decider opens the Store again; a thief of the writer process could have
rewritten its files. The decider is anchored at the open when it holds no certified head, when the
opened World's head IS the last certified one, or when the step pairs between them, read from the
Store's kept records, advance the last certified chain to the opened World's chain
(`anchoredBy`: `chainOf` over the pairs, the kernel's own link). Where the pairs come from does not
matter: a chain match binds the opened World's history to the certified head (`fold_head_binds`),
so a rewritten Store anchors only if its history extends the certified one. A World BEHIND the last
certified head is anchored when its fold reaches that step count with that head (`absorb`), never
otherwise. An unanchored decider certifies nothing and serves residents as before.

It names no key and holds no seed: whose key signs is keybroker's slot; whether that key is in the
World's authority is the writer's (it finds the signer's index there) and the joiner's
(`Head.certified`) business.
-/
import Protocol.Head
import Hosting.BrokerWire

namespace Nanodregg.Hosting.Certify

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol.Head


/-- The writer's socket directory under keybroker's SOCKDIR: a leading dot, so no grain directory
name can take it (`Codec.Path`'s components and `grain_name_ok` refuse one). -/
def writerDir : String := ".writer"

/-- The writer's socket, alone in `writerDir` (the sandbox's connect rule exposes the directory). -/
def certifySock : String := "certify.sock"

/-- The most record-end heads a decider holds: a certify ask names the base the writer has just
sealed, a few records behind the decider's tip at most; an older one is `notOnFold`. -/
def headsMax : Nat := 4096

/-- The decider's view of its own fold, for certifying. -/
structure Certifier (D : Type) where
  origin : D
  /-- the heads at the last record ends absorbed, ascending, the tip last, at most `headsMax` -/
  heads : List (Head D)
  /-- the last head this key certified (persisted by keybroker, read back at a restart) -/
  last : Option (Head D)
  /-- the fold this decider holds passes through `last` -/
  anchored : Bool

variable {D : Type} [Ord D] [DecidableEq D]

/-- The step pairs between step counts `s` and `t` of a log whose pairs, in order, start after step
`from_`: exactly `t - s` of them, or `none` when the log does not reach back to `s` or on to `t`. -/
def pairsBetween (from_ s t : Nat) (pairs : List (Step D × D)) : Option (List (Step D × D)) :=
  if from_ ≤ s ∧ s ≤ t then
    let ps := (pairs.drop (s - from_)).take (t - s)
    if ps.length = t - s then some ps else none
  else none

/-- The step pairs `ps` advance the certified head `l`'s chain to `w`'s chain: one World, `w` exactly
`ps.length` steps past `l`, and the kernel's chain link (`chainOf`) over the pairs from `l.chain`
reaching `w.chain`. -/
def anchoredBy (E : Env D) (l : Head D) (w : World D) (ps : List (Step D × D)) : Bool :=
  decide (l.origin = w.origin ∧ l.steps + ps.length = w.steps ∧ chainOf E l.chain ps = w.chain)

/-- The certifier of a decider that opened the Store at `w`, holding the last certified head `last`;
`pairs` are the step pairs from `last` to `w` when the Store keeps them (see ANCHORING). -/
def Certifier.opened (E : Env D) (w : World D) (last : Option (Head D)) (pairs : Option (List (Step D × D))) :
    Certifier D :=
  let h := headOf E w
  { origin := w.origin, heads := [h], last,
    anchored := match last with
      | none => true
      | some l => decide (h = l) || (match pairs with | some ps => anchoredBy E l w ps | none => false) }

/-- One more record end of the decider's own fold: its head joins the window (the oldest leaves past
`headsMax`), and a fold that reaches the last certified head WITH that head is anchored. A certifier
holding no head is anchored at its open or never (a last-certified file it could not read). -/
def Certifier.absorb (c : Certifier D) (h : Head D) : Certifier D :=
  { c with heads := (c.heads ++ [h]).drop (c.heads.length + 1 - headsMax),
           anchored := c.anchored || (match c.last with | some l => decide (h = l) | none => false) }

/-- THE decision for one certify ask: the bytes to sign, and the certifier that has certified them. -/
def decide (X : Ctx D) (c : Certifier D) (b : ByteArray) : Except Broker.Refusal (Certifier D × ByteArray) := do
  let some h := certifiedSaid X b | throw .badCertify
  unless certifiedBytes X.env h = some b do throw .badCertify
  if h.origin ≠ c.origin then throw .notOnFold
  unless c.anchored do throw .unanchored
  if let some l := c.last then
    if h.steps < l.steps ∨ (h.steps = l.steps ∧ h ≠ l) then throw .regressed
  match c.heads.getLast? with
  | some t => if t.steps < h.steps then throw .notYet
  | none => throw .notYet
  unless c.heads.contains h do throw .notOnFold
  pure ({ c with last := some h }, b)

end Nanodregg.Hosting.Certify
