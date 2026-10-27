/-
# Spec.Proofs.Claims — what nanodregg is FOR, as predicates on a `System`

The top-level statements (redregg/work/promo/TOPLEVEL-SPEC.md §2–§8), each a `Prop` over the
record of deployed entry points (`Spec.System`). `Spec.Proofs.Floor` refutes each one on a trivial
system and inhabits it with a deployed run; that is the tree's whole vacuity obligation: a lemma
under a top theorem carries meaning only through the claim it proves, whatever its own shape.
`Spec.Proofs.Deployed` proves `Claim (deployed d)` where the composition exists.

Premises that are true of the deployed system only under an assumption the system does not yet
discharge are PARAMETERS of the claim, named (a relay, a restriction to `NoRef` laws), never hidden
in a definition. Removing one is a strengthening the checker sees.

This module lives under `Proofs` because a claim is a statement (closure C3); it defines no
function.
-/
import Spec.System
import Kernel.Proofs.Rederive
import Kernel.Proofs.Fold
import Kernel.Proofs.Cells
import Kernel.Proofs.Logic.History
import Kernel.Proofs.WriteNext
import Lang.Proofs.Chain
import Lang.Proofs.Receiver
import Protocol.Proofs.Behind

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The vocabulary -/

/-- Every step of the log is the system's own decision of its own event on the World before it: a
Turn is what `receive` derives from the call its event decodes to, a refusal is what `recordedBy`
records for it. (`Receive.Honest`, with the kernel a parameter.) -/
def Decided (S : System D) : World D → List (Step D) → Prop
  | _, [] => True
  | w, .turn t :: rest => ∃ c, S.X.decodeCall t.event = some c ∧ S.receive w c = .ok t ∧
      ∀ w', S.admit w t = .ok w' → Decided S w' rest
  | w, .refusal r :: rest => ∃ c v w₁, S.X.decodeCall r.event = some c ∧
      S.recordedBy w c r = .recorded v r w₁ ∧ ∀ w', S.refuse w r = .ok w' → Decided S w' rest

/-- An audited log: it folds under the system's kernel to `w'`, and every step is the kernel's
own decision. -/
def Audited (S : System D) (w : World D) (l : List (Step D)) (w' : World D) : Prop :=
  S.fold w l = .ok w' ∧ Decided S w l

/-- A World a member's follower may start from: a genesis World (built by the kernel from the
signed inputs), or a base whose bytes hash to the pin of an invitation that the sponsor key the
member trusts signed, for the member's own World (thin consent: the history before the pin is the
sponsor's word, PROTOCOL-14). -/
inductive Start (S : System D) (me : Command.Self D) (trusted : ByteArray) : World D → Prop
  | genesis (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
      (auth : Authority) : Start S me trusted (genesisWorld S.X name nonce allowance founders auth)
  | pinned {inv : ByteArray} {i : Invite.Invitation D} {w : World D} :
      Command.adoptPin S.X me inv trusted = .ok i →
      S.B.digest (S.B.world.bytes w) = i.pin.digest → S.B.stepsOf w = i.pin.steps →
      w.origin = me.world → Start S me trusted w

/-- The relay assumption the deployed follower needs today: every continuation the relay hands
follow that parses as `adopt INVITE KEY` names the sponsor key the member trusts. (The continuation
is client-held bytes; under an arbitrary relay a forged `adopt` names the forger's key, and the pin
it signs is any World. TOPLEVEL-SPEC §11.2 removes this premise by keeping the command's state
inside follow.) -/
def keyFaithful (S : System D) (trusted kb : ByteArray) : Prop :=
  ∀ st inv key, Command.State.ofBytes kb = some st →
    Command.parse S.X.digestOf st.argv = .ok (Command.Cmd.adopt inv key) → key = trusted

/-- One frame of the member's follower, from a World to a World: any memory, any result the
Host returns, and any continuation the relay allows. -/
def Moves (S : System D) (relay : ByteArray → ByteArray → Prop) (me : Command.Self D)
    (trusted : ByteArray) (w w' : World D) : Prop :=
  ∃ (f f' : Command.Follow D) (kb res : ByteArray) (p : Command.Persist D) (r : Command.Reply),
    relay trusted kb ∧ f.world = w ∧ S.follow me f kb res = (f', p, r) ∧ f'.world = w'

/-- Any number of frames (any interleaving of the member's commands). -/
inductive Reach (S : System D) (relay : ByteArray → ByteArray → Prop) (me : Command.Self D)
    (trusted : ByteArray) : World D → World D → Prop
  | refl (w : World D) : Reach S relay me trusted w w
  | tail {w w₁ w₂ : World D} : Reach S relay me trusted w w₁ → Moves S relay me trusted w₁ w₂ →
      Reach S relay me trusted w w₂

/-! ## §2 ONE HISTORY (the apex, with §3) -/

/-- **A1. The member's World is an audited fold from a start.** Whatever frames follow is fed —
any Host replies, any continuation the relay allows, any interleaving of the member's commands —
the World it holds is an audited log's fold from a start (`∃ w₁`: an adopt replaces a World that
holds nothing by a pinned base, a new start). -/
def OneHistory.member (S : System D) (relay : ByteArray → ByteArray → Prop) : Prop :=
  ∀ (me : Command.Self D) (trusted : ByteArray) (w₀ w : World D), Start S me trusted w₀ →
    Reach S relay me trusted w₀ w → ∃ w₁ l, Start S me trusted w₁ ∧ Audited S w₁ l w

/-- **A2. Two logs the kernel folds from one World, agreeing on step count and chain, reach one
World**, or the hash collides among the two folds' link inputs. (Any folds, audited or not: the
chain binds what was folded, whoever decided it.) -/
def OneHistory.pair (S : System D) : Prop :=
  ∀ {g wf wg : World D} {lf lg : List (Step D)}, S.fold g lf = .ok wf → S.fold g lg = .ok wg →
    wf.steps = wg.steps → wf.chain = wg.chain →
      wf = wg ∨ CollidesAmong S.X.env.hash (foldPres S.X.env g lf ++ foldPres S.X.env g lg)

/-! ## §3 INTEGRITY — what "the kernel's own decision" means -/

/-- **B2. Value.** Along any log the kernel folds (audited or not: conservation does not depend on
authority), every denomination's balance sum is unchanged, and so is its floor sum unless a Turn
of the log created the denomination's well. -/
def Integrity.value (S : System D) : Prop :=
  ∀ {w w' : World D} {l : List (Step D)}, w.Canon S.X.env → S.fold w l = .ok w' → ∀ d,
    w'.valueSum d = w.valueSum d ∧
      ((∀ t ∈ Step.turns l, d ∉ (createdIds t).map S.X.env.bytes) → w'.floorSum d = w.floorSum d)

/-- **B3. Law (what an object's author is promised), for `NoRef` laws.** Along an audited log, an
object live at the start has a history of judged steps (`ObjectHistory`), its package never
changes, and EVERY history of it between the two Worlds in whose judged steps a `NoRef` law `t` of
its package is in force is a chain of steps the law's reference meaning admits (`Std.Step [] t`,
the `BigStep` semantics), each paired with the request that made it. Every history, not some: a
judged step carries the view of the call that made it, and a step of another call reaching the same
World with a view that lacks the law makes "some history" vacuous; excluding it is a collision over
an unbounded preimage set, so the existential form (SPEC-2) had no floor against a kernel no law
judges (`floor_integrity_lawChain`). The restriction to `NoRef` is the premise TOPLEVEL-SPEC §11.6
removes. -/
def Integrity.law (S : System D) : Prop :=
  ∀ {obj law : D} {p : Lang.Package} {fs : List (Lang.Label × Lang.Term)} {ℓ : Lang.Label}
    {t : Lang.Term}, p.body = .record fs → ℓ ∈ p.laws → Lang.Row.find? ℓ fs = some t →
    Lang.IsLaw t → Lang.NoRef t →
    ∀ {w w' : World D} {l : List (Step D)}, Audited S w l w' → CellsCanon S.X.env w →
    ∀ {cell : Cell}, w.live S.X.env obj = some cell → cell.kind = kindObject →
      (∃ tr, ObjectHistory S.X obj w w' tr) ∧
        (∃ cell', w'.live S.X.env obj = some cell' ∧ packageOf S.X obj cell' = packageOf S.X obj cell) ∧
        ∀ tr, ObjectHistory S.X obj w w' tr →
          (∀ e ∈ tr, law ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 law = .ok p) →
          ∀ {o : Lang.Data}, Lang.readState S.X.digestOf (Lang.recordRow p.state) (stateOf cell) = .ok o →
            ∃ steps, Lang.Std.Chain (Lang.Std.Step [] t) o steps ∧
              tr.map (fun e => (Lang.reqData S.X.env.bytes e.2.2.2.1,
                Lang.readState S.X.digestOf (Lang.recordRow p.state) e.2.2.2.2.2.1)) =
                steps.map (fun s => (s.1, .ok s.2))

/-! ## §4 CONSENT AND SETTLEMENT — what a member is promised of its own follower -/

/-- **C(ii), submit-class. `ok` means committed.** A follow step that ends a command `done ok` at
the settle phase (4) means follow's own World journals the call the continuation carries. -/
def Consent.okCommitted (S : System D) : Prop :=
  ∀ (me : Command.Self D) (f f' : Command.Follow D) (kb res o e : ByteArray) (p : Command.Persist D)
    (argv acc : List ByteArray), Command.State.ofBytes kb = some ⟨argv, 4, acc⟩ →
    S.follow me f kb res = (f', p, .done CommandExit.ok.code.toUInt8 o e) →
    ∃ cb c hh td, acc.getLast? = some cb ∧ S.X.decodeCall cb = some c ∧
      f.world.journalAt S.X.env (txIdOf S.X c) = some (hh, td)

/-- **C(iii). Final is final.** A settlement follow prints as `expired`, or `refused` by a name
other than `stale`, is never contradicted: on no extension of the log does the writer admit the
call. (`refused stale` is final only for the member's own planned call and up to a collision:
`staleBehind_final`, a separate claim.) -/
def Consent.final (S : System D) : Prop :=
  ∀ (me : Command.Self D) {w w' : World D} (c : Call D) {l : List (Step D)},
    w.RefusalsCanon S.X.env → w.JournalCanon S.X.env →
    (S.settle me w c = .expired ∨ ∃ code, code ≠ staleCode ∧ S.settle me w c = .refused code) →
    S.fold w l = .ok w' → ∀ out, S.submit w' c ≠ .ok out

/-- **C(ii), cancel. `ok` means cancelled on the member's own World.** A follow step of a
`cancel CALL` command that ends `done ok` leaves follow at a World whose settlement of the call is
`refused cancelled`: the writer's word that it recorded the cancel is never enough (collation A7). -/
def Consent.cancelOk (S : System D) : Prop :=
  ∀ (me : Command.Self D) (f f' : Command.Follow D) (kb res o e : ByteArray) (p : Command.Persist D)
    (st : Command.State) (cb : ByteArray), Command.State.ofBytes kb = some st →
    Command.parse S.X.digestOf st.argv = .ok (Command.Cmd.cancel cb) →
    S.follow me f kb res = (f', p, .done CommandExit.ok.code.toUInt8 o e) →
    ∃ c, S.X.decodeCall cb = some c ∧ S.settle me f'.world c = .refused (Command.cancelledCode (D := D))

/-- **C(iii), stale. `refused stale` is final for the member's own call.** A call the member's
follower planned at a World `w₀` of its fold (`signedReads`, `plan`), that a later World `w` of the
fold settles `refused stale`, is admitted by no `submit` at any World the fold reaches from `w` —
or the hash collides among the call's pin inputs at `w₀` and there (`behindPres`, an explicit list). -/
def Consent.staleFinal (S : System D) : Prop :=
  ∀ (me : Command.Self D) {w₀ w w' : World D} {l₁ l₂ : List (Step D)} {key : ByteArray}
    {cmd : Command.Cmd D} {rs : Command.SignedReads D} {b : Body D} {u : Unsigned D} (c : Call D),
    w₀.CellsFit Codec.Kernel.Cell.Fits S.X.env → w₀.RowsCanon S.X.env → w₀.RowsOk S.X.env →
    Command.signedReads S.X w₀ cmd = .ok rs → Command.plan S.X me w₀ key rs b = .ok u → c.unsigned = u →
    w.RefusalsCanon S.X.env → w.JournalCanon S.X.env →
    S.fold w₀ l₁ = .ok w → S.fold w l₂ = .ok w' → S.settle me w c = .refused staleCode →
    (∀ out, S.submit w' c ≠ .ok out) ∨ CollidesAmong S.X.env.hash (Command.behindPres S.X.env w₀ w' u)

/-! ## §8 WHAT A NON-MEMBER IS SHOWN -/

/-- **G2. Nothing of the log is shown past a failed envelope.** The writer defers a frame (answers
it with a page of the log or of a base) only when its payload is an envelope `Envelope.check`
passes on the writer's World: this World, a window inside the bound, the member's current key,
a verifying signature, a live follow grant chain, the height inside the window. -/
def Shown.onlyFollowers (S : System D) : Prop :=
  ∀ (w : World D) (f : Host.Frame) (d : Host.Deferred), S.handle w f = .defer d →
    ∃ e, Envelope.ofBytes S.X f.payload = some e ∧ Envelope.check S.X w e = .ok ()

end Nanodregg.Spec
