/-
# Ledger.Proofs.EscrowInvokes — the escrow pays out at most once over the history the World admits

`escrow_runs_one_payout` (Ledger.Proofs.EscrowRun) bounds the payouts of a `Runs` chain: runs the
receiver commits, each next run reading slots that hold, key by key, what the run before it wrote.
Here the chain is the World's: `Invokes X obj pkg p w invs` is a history of admitted turns around
one object `obj`, each either a signed top-level invoke of `obj` (received on the World the last turn
was admitted to, and admitted) or a turn that neither touches nor creates `obj`. KERNEL proves the
links (`Kernel.Proofs.InvokeNext`, `Kernel.Proofs.Frame`): the judge admitted each invoke's run
(`invoke_next_judged`), the object's live state after it holds what the run returned
(`invoke_next_slots`), another turn leaves the object's entry (`admit_frame`), and the next invoke
runs on the live cell (`invokeRun_live`). So:

* `invokes_runs`: such a history is a `Runs` from the state the object holds;
* `escrow_invokes_one_payout`: along any such history on an object whose package reads as `escrow` in
  each invoke's view, at most one call the invokes return is a payout, at a lawful `Ctx` whose
  program is the language over its own codec; `escrow_invokes_deployed` at the node's
  (`Host.Deployed.X`), premise only the history.

Not covered: a turn that touches `obj` other than as its top-level invoke (an invoke of `obj` nested
in another object's call tree, KERNEL's cv 01a15430-0f62, or any other touch) is not a step of
`Invokes`; a history with one is not an instance. The teeth are `Ledger.Proofs.EscrowWitness`'s:
`escrow_link_bites` (without the next-state link an admitted payout repeats) and
`escrow_second_release_refused` (without the judge a release from `released` pays again).
-/
import Ledger.Proofs.EscrowWitness
import Kernel.Proofs.InvokeNext

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Lang
open Nanodregg.Kernel Nanodregg.Kernel.Receive
open Nanodregg.Ledger.Escrow

section
variable {D : Type} [Ord D] [DecidableEq D]

/-- **A history the World admits around one object.** Each step is one admitted turn: either a
signed top-level invoke of `obj` (a call `c` received on `w`, `receive X w c = .ok t`, admitted to
`w'`, whose body invokes `obj`, whose `invokeRun` reads the object's cell naming package `pkg`, read as
`p` in the call's view, and whose run on the cell's state at the call's budget returned `calls`), or
any other admitted turn that neither touches nor creates `obj` (its calls are not counted: it runs
no method of `obj`). The list holds the invokes' calls, in order. -/
inductive Invokes (X : Ctx D) (obj pkg : D) (p : Package) : World D → List (List (Body D)) → Prop
  | nil (w : World D) : Invokes X obj pkg p w []
  | invoke {w w' : World D} {c : Call D} {t : Turn D} {method : Nat} {args : ByteArray} {budget : Nat}
      {via : Option D} {cell : Cell} {r : Req D} {s : Slots} {calls : List (Body D)}
      {rows : List (RowSlot D × RowAct)} {used : Nat} {rest : List (List (Body D))} :
      receive X w c = .ok t → World.admit X.env w t = .ok w' →
      c.unsigned.body = .invoke obj method args budget via →
      invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, pkg, r) →
      readPackage (pinned X.env w c.unsigned.pins) pkg = .ok p →
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) pkg (stateOf cell)
        method args r (min budget (poolOf c.unsigned.body)) = .ok (s, calls, rows, used) →
      Invokes X obj pkg p w' rest → Invokes X obj pkg p w (calls :: rest)
  | other {w w' : World D} {t : Turn D} {rest : List (List (Body D))} :
      World.admit X.env w t = .ok w' → (∀ x ∈ t.touches, x.cell ≠ obj) → obj ∉ createdIds t →
      Invokes X obj pkg p w' rest → Invokes X obj pkg p w rest

/-- **An admitted history around one object is a chain of committed runs**, from the state the
object holds: a turn that neither touches nor creates it leaves its entry (`admit_frame`); an
invoke runs on the live cell (`invokeRun_live`), the judge admitted it (`invoke_next_judged`), and
the object's next live state holds, key by key, what the run returned (`invoke_next_slots`). -/
theorem invokes_runs {X : Ctx D} {obj pkg : D} {p : Package} :
    ∀ {w : World D} {invs : List (List (Body D))}, Invokes X obj pkg p w invs →
      invs = [] ∨ ∃ cell, w.live X.env obj = some cell ∧ Runs X.program pkg p (stateOf cell) invs
  | _, _, .nil _ => .inl rfl
  | _, _, .other ha hl hc h => by
    have he : _ = _ := admit_frame (c := obj) ha (fun x hx hxc => absurd hxc (hl x hx)) hc
    rcases invokes_runs h with h | ⟨cell, hlive, hr⟩
    · exact .inl h
    · refine .inr ⟨cell, ?_, hr⟩
      unfold World.live at hlive ⊢
      rw [← he]
      exact hlive
  | _, _, .invoke hc ha hb hr hrd hp htail => by
    obtain ⟨laws, hj⟩ := invoke_next_judged hc ha hb hr hp
    obtain ⟨cell', hlive', hk⟩ := invoke_next_slots hc ha hb hr hp
    refine .inr ⟨_, invokeRun_live hr, ?_⟩
    rcases invokes_runs htail with rfl | ⟨cell'', hlive'', hruns⟩
    · exact .cons hrd hp hj (fun _ => rfl) (.nil _)
    · rw [hlive'] at hlive''
      cases hlive''
      exact .cons hrd hp hj hk hruns

/-- **The escrow pays out at most once over the invokes the World admits.** Along any sequence of
signed invokes of one object, each received on the World the last was admitted to and admitted,
whose package reads as `escrow` in each invoke's view, at most one call the runs return is a
payout, at a lawful `Ctx` whose program is the language over its own codec. -/
theorem escrow_invokes_one_payout {X : Ctx D} (hX : X.Lawful)
    (hprog : X.program = Lang.program X.env.bytes X.digestOf) {obj pkg : D} {w : World D}
    {invs : List (List (Body D))} (h : Invokes X obj pkg escrow w invs) : payoutCalls invs ≤ 1 := by
  rcases invokes_runs h with rfl | ⟨_, _, hruns⟩
  · simp [payoutCalls]
  · exact escrow_program_one_payout hX hprog hruns

end

/-- **Deployed**: along any sequence of invokes the node (`Host.Deployed.X`) admits on one object
whose package reads as `escrow` in each invoke's view, at most one returned call is a payout; no
premise but the invokes. -/
theorem escrow_invokes_deployed {obj pkg : Codec.Digest} {w : World Codec.Digest}
    {invs : List (List (Body Codec.Digest))}
    (h : Invokes (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)) obj pkg escrow w invs) :
    payoutCalls invs ≤ 1 :=
  escrow_invokes_one_payout (deployed_ctx_lawful _) rfl h

end Nanodregg.Ledger.Proofs
