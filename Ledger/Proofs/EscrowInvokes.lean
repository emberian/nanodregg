/-
# Ledger.Proofs.EscrowInvokes — the escrow pays out at most once over the history the World admits

`escrow_runs_one_payout` (Ledger.Proofs.EscrowRun) bounds the payouts of a `Runs` chain: runs the
receiver commits, each next run reading slots that hold, key by key, what the run before it wrote.
Here the chain is the World's: an `ObjectHistory` around one escrow object (KERNEL's
`Kernel.Proofs.Logic.History`: every step of the World, as the object sees it; a step that leaves
it alone records nothing, a step that judges it records what the judge saw). KERNEL lifts it once
(`object_history_chain`): the judged steps are a `Std.Chain` of the escrow law's admitted steps from
the object's state, and each invoke's calls are its run's (`object_history_runs`). So:

* `escrow_invokes_one_payout`: along any `ObjectHistory` of an object whose every judged step was
  judged by the escrow package (read as `escrow` in the step's view), at most one call the invokes
  return is a payout, at a lawful `Ctx` whose program is the language over its own codec:
  `payoutCalls_le_one`, `chain_count` of the steps into a settled state. `escrow_invokes_deployed`
  at the node's (`Host.Deployed.X`), premises only the history and its package reading.
* Completeness: an honest folded log is such a history (`object_history_of_honest`), and a history files no
  invoke of the object as a step that left it alone (`ObjectStep.keep` says "no invoke"; `other`
  and `frame` exclude a touch of it), so the count is of every invoke the log holds.

The history covers every invoke of the object, signed or NESTED in another object's call tree
(`ObjectStep.nested`), and every other turn and recorded refusal (the hand-rolled `Invokes`, which
covered only signed top-level invokes, is deleted: it was this instance). The teeth are
`Ledger.Proofs.EscrowWitness`'s: `escrow_link_bites` (without the next-state link an admitted
payout repeats) and `escrow_second_release_refused` (without the judge a release from `released`
pays again). The premises hold together, with the bound attained, through the real `receive` and
`World.admit`: `Ledger.Proofs.EscrowAdmitted.escrow_history_witnessed` (a deposit through a grant
capped at the escrow's amount, then a release; LEDGER-18).
-/
import Ledger.Proofs.EscrowWitness
import Kernel.Proofs.Logic.History

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Lang
open Nanodregg.Kernel Nanodregg.Kernel.Receive
open Nanodregg.Ledger.Escrow

section
variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- The judged steps of a history, paired with the chain's steps the lift reads them as. -/
private theorem pair_steps {digestOf : ByteArray → Option D} {bytesOf : D → ByteArray} {row : List (Label × Ty)} :
    ∀ (tr : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D)))
      (steps : List (Data × Data)),
      tr.map (fun e => (reqData bytesOf e.2.2.2.1, readState digestOf row e.2.2.2.2.2.1)) =
        steps.map (fun s => (s.1, .ok s.2)) →
      ∃ ps : List (List (Body D) × (Data × Data)), ps.map Prod.fst = tr.map (fun e => e.2.2.2.2.2.2) ∧
        ps.map Prod.snd = steps ∧
        ∀ x ∈ ps, ∃ e ∈ tr, x.1 = e.2.2.2.2.2.2 ∧ readState digestOf row e.2.2.2.2.2.1 = .ok x.2.2
  | [], [], _ => ⟨[], rfl, rfl, by simp⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | e :: tr, s :: steps, h => by
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, hn⟩, h⟩ := h
      obtain ⟨ps, h1, h2, h3⟩ := pair_steps tr steps h
      refine ⟨(e.2.2.2.2.2.2, s) :: ps, by simp [h1], by simp [h2], fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨e, List.mem_cons_self .., rfl, hn⟩
      · obtain ⟨e', he', h4, h5⟩ := h3 x hx
        exact ⟨e', List.mem_cons_of_mem _ he', h4, h5⟩

/-- **The escrow pays out at most once over the history the World admits.** Along any
`ObjectHistory` of one object (its signed and nested invokes, writes, law changes, every other turn
and recorded refusal) whose every judged step was judged by the package `pkg`, read as `escrow` in
that step's view, at most one call the invokes return is a payout, at a lawful `Ctx` whose program
is the language over its own codec. -/
theorem escrow_invokes_one_payout {rc : Lang.ReceiptCheck} {X : Ctx D} (hX : X.Lawful)
    (hprog : X.program = Lang.program X.env.bytes X.digestOf rc) {obj pkg : D} {w w' : World D}
    {tr : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))}
    (h : ObjectHistory X obj w w' tr)
    (hpkg : ∀ e ∈ tr, e.2.1 = some pkg ∧ readPackage e.1 pkg = .ok escrow) :
    payoutCalls (tr.map fun e => e.2.2.2.2.2.2) ≤ 1 := by
  by_cases hne : tr = []
  · subst hne; simp [payoutCalls]
  have hin : ∀ e ∈ tr, pkg ∈ e.2.1.toList ++ e.2.2.1 ∧ readPackage e.1 pkg = .ok escrow := fun e he => by
    obtain ⟨h1, h2⟩ := hpkg e he
    exact ⟨by rw [h1]; simp, h2⟩
  obtain ⟨cell, o, hl, ho⟩ := object_history_start hX hprog h hin hne
  obtain ⟨steps, hc, hmap⟩ := object_history_chain hX hprog escrow_body (by rw [escrow_laws]; simp)
    escrow_field escrow_law_isLaw escrow_law_noRef h hin hl ho
  obtain ⟨ps, hfst, hsnd, hpair⟩ := pair_steps tr steps hmap
  have hruns := object_history_runs h
  rw [← hfst]
  have hca : Std.Chain (Std.Admits [] law) o (ps.map Prod.snd) := by
    rw [hsnd]
    exact Std.chain_mono (R := Std.Step [] law) (fun _ _ _ hs => hs.1) hc
  refine payoutCalls_le_one ps hca (fun x hx => ?_)
  obtain ⟨e, he, hcalls, hn⟩ := hpair x hx
  obtain ⟨rv, method, args, fuel, rows, used, -, hrun⟩ := (hruns e he).2 pkg (hpkg e he).1
  rw [hcalls]
  exact runCalls_payout (escrow_program_calls hX hprog (hpkg e he).2 hrun) hn

end

/-- **Deployed**: along any history the node (`Host.Deployed.X`) admits around one object whose
every judged step was judged by a package read as `escrow`, at most one returned call is a payout;
premises: the history and that package reading, the `Ctx` discharged (`deployed_ctx_lawful`, `rfl`). -/
theorem escrow_invokes_deployed {rc : Lang.ReceiptCheck} {obj pkg : Codec.Digest} {w w' : World Codec.Digest}
    {tr : List (Pinned Codec.Digest × Option Codec.Digest × List Codec.Digest × Req Codec.Digest × Slots × Slots ×
      List (Body Codec.Digest))}
    (h : ObjectHistory (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes? rc)) obj w w' tr)
    (hpkg : ∀ e ∈ tr, e.2.1 = some pkg ∧ readPackage e.1 pkg = .ok escrow) :
    payoutCalls (tr.map fun e => e.2.2.2.2.2.2) ≤ 1 :=
  escrow_invokes_one_payout (deployed_ctx_lawful _) rfl h hpkg

end Nanodregg.Ledger.Proofs
