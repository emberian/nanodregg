/-
# Kernel.Proofs.Logic.Claims — B4, the claim clause of INTEGRITY (KERNEL-73; DESIGN-PCC §3.3(c), §4)

A package carries claims in its identity (`Lang.Package.claims`, LANG-93) and the install check refuses
a claim the term does not bear (`Lang.checkClaims`; `Lang.install_claims`). This module is the World
half: **every claim a package carries holds of every object of it along every audited log**, for the
fragment the checker decides.

`object_history_keeps`: at a lawful `Ctx` running the language, take a package `p` whose field check
admitted (as install's does, `Lang.checkInstall_fields`) and which claims `keeps inv ℓ`. Then its body is
a record literal holding the invariant as `lam S ib` and the law `ℓ` as a literal, and along any
`ObjectHistory` in whose every judged step the law's id reads as `p` and is among the judging laws, from a
live object whose state keeps `ib` (the seed: `create` judges it as a birth, which the shape does not
exempt), every judged step's new state reads at the state type and keeps `ib`. The proof is THE LIFT
(`object_history_chain`: the history is a `Std.Chain` of the law's steps) composed with the term half
(`Lang.chain_keeps`: along such a chain the invariant is kept once it holds).

Premises are B3's (`object_history_chain`: a `NoRef` law, in force at every judged step, read as `p` in
every view) plus the claim, the field check and the start state. The start state is a premise, not a
theorem of the birth, because an `ObjectHistory` begins at a live object; the birth's judgment is the
row's (journey LK5: created at 0, which keeps `le100`). FLOOR (DESIGN-PCC §4): `uncheckedInstallKernel`,
the plant `skip-claims` (journey `Mode.skipClaims`), under which a package claiming `keeps le100 bounded`
by a law that admits every write installs and `set 101` is admitted (row LK6 flips); this theorem's
`hchk` is what that kernel lacks.
-/
import Kernel.Proofs.Logic.History
import Lang.Proofs.Claim

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **B4 for `keeps`: a claim a package carries holds of every object of it along every audited log.**
The package's field check admitted and it claims `keeps inv ℓ`; its body is then a record `fs` holding
`inv` as `lam S ib`, and along any `ObjectHistory` in whose every judged step the law `law` reads as `p`
and is in force, from a live object whose state reads `o` and keeps `ib`, every judged step's new state
reads at the state type and keeps `ib`. `hnr`: the law's literal mentions no closure package (B3's
premise, as `object_history_chain` takes it). -/
theorem object_history_keeps {rc : Lang.ReceiptCheck} {X : Ctx D} (hX : X.Lawful)
    (hprog : X.program = Lang.program X.env.bytes X.digestOf rc)
    {obj law : D} {p : Lang.Package} {inv ℓ : Lang.Label}
    (hchk : p.checkFields = .ok ()) (hcl : Lang.Claim.keeps inv ℓ ∈ p.claims)
    (hnr : ∀ fs t, p.body = .record fs → Lang.Row.find? ℓ fs = some t → Lang.NoRef t) :
    ∃ fs ib, p.body = .record fs ∧ Lang.Row.find? inv fs = some (.lam p.state ib) ∧
      ∀ {w w' : World D} {tr : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))},
        ObjectHistory X obj w w' tr →
        (∀ e ∈ tr, law ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 law = .ok p) →
        ∀ {cell : Cell} {o : Lang.Data}, w.live X.env obj = some cell →
          Lang.readState X.digestOf (Lang.recordRow p.state) (stateOf cell) = .ok o →
          Lang.Keeps [] ib o →
          ∀ e ∈ tr, ∃ n, Lang.readState X.digestOf (Lang.recordRow p.state) e.2.2.2.2.2.1 = .ok n ∧
            Lang.Keeps [] ib n := by
  obtain ⟨hl, -, fs, ib, b, hb, hi, hf, hg⟩ := Lang.checkFields_claim hchk hcl
  refine ⟨fs, ib, hb, hi, ?_⟩
  intro w w' tr h hin cell o hlive ho h0
  have hlaw : Lang.IsLaw (.lam p.state (.lam p.state (.lam Lang.reqTy b))) := ⟨_, _, _, _, rfl⟩
  obtain ⟨steps, hch, hmap⟩ :=
    object_history_chain hX hprog hb hl hf hlaw (hnr fs _ hb hf) h hin hlive ho
  have hk := Lang.chain_keeps hg h0 hch
  intro e he
  have hmem : (Lang.reqData X.env.bytes e.2.2.2.1,
      Lang.readState X.digestOf (Lang.recordRow p.state) e.2.2.2.2.2.1) ∈
        steps.map (fun s => (s.1, Except.ok s.2)) := by
    rw [← hmap]
    exact List.mem_map_of_mem he
  obtain ⟨s, hs, hse⟩ := List.mem_map.1 hmem
  exact ⟨s.2, (congrArg Prod.snd hse).symm, hk s hs⟩

end Nanodregg.Kernel.Receive
