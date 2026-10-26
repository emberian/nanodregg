/-
# Protocol.Proofs.Foreign — what a receipt column means (E5)

`foreign_receipt_sound` (P2): when the deployed check shows a receipt `committed` against a head
object whose roots are those of a World folded from A's genesis, the transaction was ADMITTED in
that fold: a Turn of the log, with that transaction id, admitted after a prefix that folds to `v`,
at height `v.height + 1`, with that turn digest; or the hash collides among a LISTED set
(`check_committed`'s). The premise `hr` is the one this theorem cannot discharge and nothing in B
can: the held head is the head of a fold of A (head freshness and the poster's honesty, the
thin-member trust of PROTOCOL-42). B holds A head, not THE head; `forkedHead` narrows it only to
"no two posters of this object disagreed at one step count".

`forged_receipt_refused` (P3): a receipt at the right head that states an entry the World does not
hold is refused `pathMismatch`, or the hash collides. `forked_head_column_refused` (P4): a recorded
fork checks no receipt. `refused_receipt_notCommitted` (P5): a receipt that checks `refused` is
refused `notCommitted`, and is the World's recorded refusal (`check_refused_sound`), or the hash
collides (journey row RC3).
-/
import Protocol.Foreign
import Protocol.Proofs.Receipt
import Kernel.Proofs.Journal

namespace Nanodregg.Protocol.Foreign

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec Nanodregg.Protocol.Receipt

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] in
theorem check_committed_of {E : Env D} {dc : Stream D} {cell : Cell} {rb : ByteArray} {s : Lang.Seen}
    (hk : check E dc cell rb = .ok s) :
    ∃ w c₀ h₀ rootsB s₀ roots r td,
      Lang.headView (fun b => (dc.decode b).toOption) (E.bytes (headPackageId E)) cell =
        some (.at w c₀ h₀ rootsB s₀) ∧
      (dc.decode rootsB).toOption = some roots ∧ Receipt.ofBytes E dc rb = some r ∧
      Receipt.check E h₀ roots r.txId 0 r = .ok (.committed s.height td) ∧
      s.turn = E.bytes td ∧ s.tx = E.bytes r.txId := by
  unfold check at hk
  cases hv : Lang.headView (fun b => (dc.decode b).toOption) (E.bytes (headPackageId E)) cell with
  | none => simp [hv] at hk
  | some hv' =>
    cases hv' with
    | forked w => simp [hv] at hk
    | «at» w c₀ h₀ rootsB s₀ =>
      cases hro : (dc.decode rootsB).toOption with
      | none => simp [hv, hro] at hk
      | some roots =>
        cases hrb : Receipt.ofBytes E dc rb with
        | none => simp [hv, hro, hrb] at hk
        | some r =>
          cases hc : Receipt.check E h₀ roots r.txId 0 r with
          | error e => simp [hv, hro, hrb, hc] at hk
          | ok a =>
            cases a with
            | committed h td =>
              simp [hv, hro, hrb, hc] at hk
              subst hk
              exact ⟨w, c₀, h₀, rootsB, s₀, roots, r, td, rfl, hro, rfl, hc, rfl, rfl⟩
            | refused => simp [hv, hro, hrb, hc] at hk
            | absent => simp [hv, hro, hrb, hc] at hk

theorem genesisWorld_journalAt (X : Ctx D) (name nonce : ByteArray) (a : Nat) (fs : List (ByteArray × D))
    (k : D) : (genesisWorld X name nonce a fs).journalAt X.env k = none := by
  simp [genesisWorld, World.genesis, World.journalAt, Trie.T.get, Trie.getAt]

section Sound
variable {X : Ctx D} {n : Nat} (hE : X.env.Lawful n) (hn : 0 < n)

include hE hn in
/-- **P2: a committed receipt column is an admission of A**, under the named premise `hr`. The receipt
`r` and turn digest `td` are the theorem's own (premises `hrb`, `htd`), not chosen by its conclusion, so
the collision disjunct ranges over inputs fixed by the column (GATES-20s); `check_committed_of hk` supplies
both, so the premises cost nothing. -/
theorem foreign_receipt_sound {dc : Stream D} {name nonce : ByteArray} {a : Nat}
    {fs : List (ByteArray × D)} {l : List (Kernel.Step D)} {wA : World D}
    (hA : World.fold X.env (genesisWorld X name nonce a fs) l = .ok wA)
    {cell : Cell} {rb : ByteArray} {s : Lang.Seen}
    (hk : check X.env dc cell rb = .ok s)
    (hr : ∀ w c₀ h₀ rootsB s₀,
      Lang.headView (fun b => (dc.decode b).toOption) (X.env.bytes (headPackageId X.env)) cell =
        some (.at w c₀ h₀ rootsB s₀) → (dc.decode rootsB).toOption = some (wA.roots X.env))
    {r : Receipt D} {td : D} (hrb : Receipt.ofBytes X.env dc rb = some r) (htd : s.turn = X.env.bytes td) :
    s.tx = X.env.bytes r.txId ∧
      ((∃ l₁ t l₂ v v', l = l₁ ++ Kernel.Step.turn t :: l₂ ∧
          World.fold X.env (genesisWorld X name nonce a fs) l₁ = .ok v ∧ World.admit X.env v t = .ok v' ∧
          t.txId = r.txId ∧ s.height = v.height + 1 ∧ td = turnDigest X.env t) ∨
        CollidesAmong X.env.hash ([rootsPre X.env r.root r.jroot r.rroot r.rowsroot, wA.rootsPre X.env] ++
          inclPres (journalSpec X.env) (journalPre X.env) r.txId (s.height, td) r.jpath wA.journal)) := by
  obtain ⟨w, c₀, h₀, rootsB, s₀, roots, r', td', hv, hro, hrb', hc, hturn, htx⟩ := check_committed_of hk
  have hrr : r' = r := Option.some.inj (hrb'.symm.trans hrb)
  subst hrr
  have htt : td' = td := hE.bytes_inj (hturn.symm.trans htd)
  subst htt
  have hroots : roots = wA.roots X.env := by
    have := hr w c₀ h₀ rootsB s₀ hv; rw [hro] at this; exact Option.some.inj this
  subst hroots
  have hjo := fold_journalOk (genesisWorld_journalOk X name nonce a fs) hA
  refine ⟨htx, ?_⟩
  rcases check_committed hE hn hjo.1 (reached_journal_fits hA) hc with hj | col
  · left
    rcases fold_journal_turn (genesisWorld_journalOk X name nonce a fs).1 hA hj with h0 | ⟨l₁, t, l₂, v, v', hl, hv1, hadm, htx', he⟩
    · rw [genesisWorld_journalAt] at h0; cases h0
    · simp only [Prod.mk.injEq] at he
      exact ⟨l₁, t, l₂, v, v', hl, hv1, hadm, htx', he.1, he.2⟩
  · exact .inr col


include hE hn in
/-- **P3: a forged entry is refused `pathMismatch`.** A receipt that names the held head's own roots
and states a committed entry the World does not hold is refused by its path, or the hash collides
among the listed inputs: a relay that keeps the roots cannot change the entry. -/
theorem forged_receipt_refused {dc : Stream D} {wA : World D} (hjc : wA.JournalCanon X.env)
    (hfit : ∀ k e, wA.journalAt X.env k = some e → e.1 < 2 ^ 64)
    {cell : Cell} {rb : ByteArray} {r : Receipt D} {w c₀ : ByteArray} {h₀ : Nat} {rootsB : ByteArray} {s₀ : Nat}
    (hv : Lang.headView (fun b => (dc.decode b).toOption) (X.env.bytes (headPackageId X.env)) cell =
      some (.at w c₀ h₀ rootsB s₀))
    (hro : (dc.decode rootsB).toOption = some (wA.roots X.env))
    (hrb : Receipt.ofBytes X.env dc rb = some r)
    (hroots : rootsDigest X.env r.root r.jroot r.rroot r.rowsroot = wA.roots X.env)
    {h : Nat} {td : D} (ha : r.answer = .committed h td) (hne : wA.journalAt X.env r.txId ≠ some (h, td)) :
    check X.env dc cell rb = .error "pathMismatch" ∨
      CollidesAmong X.env.hash ([rootsPre X.env r.root r.jroot r.rroot r.rowsroot, wA.rootsPre X.env] ++
        inclPres (journalSpec X.env) (journalPre X.env) r.txId (h, td) r.jpath wA.journal) := by
  cases hc : Receipt.check X.env h₀ (wA.roots X.env) r.txId 0 r with
  | ok a =>
    have ha' : a = .committed h td := by
      obtain ⟨-, -, hans⟩ := check_ok hc
      unfold answerOf at hans
      rw [ha] at hans
      simp only at hans
      split at hans
      · cases hans; rfl
      · cases hans
    subst ha'
    rcases check_committed hE hn hjc hfit hc with hj | col
    · exact absurd hj hne
    · exact .inr col
  | error e =>
    left
    have he : e = .pathMismatch := by
      unfold Receipt.check at hc
      split at hc
      · rename_i hx; exact absurd rfl hx
      · split at hc
        · rename_i hx; exact absurd hroots hx
        · unfold answerOf at hc
          rw [ha] at hc
          simp only at hc
          split at hc
          · cases hc
          · cases hc; rfl
    simp [check, hv, hro, hrb, hc, he, Receipt.Refusal.name]

include hE in
/-- **P5: a refused receipt is refused `notCommitted`, and it is A's recorded refusal.** A receipt
at the held head's roots, of a World folded from A's genesis, that checks `refused`: the deployed
column refuses it `notCommitted` (the refused arm, as an absent receipt is), and the World holds
that refusal at the call's id, with its height, code and charged member, or the hash collides among
the listed inputs (`check_refused_sound`, the receipt and the World the theorem's own). -/
theorem refused_receipt_notCommitted {dc : Stream D} {name nonce : ByteArray} {a : Nat}
    {fs : List (ByteArray × D)} {l : List (Kernel.Step D)} {wA : World D}
    (hA : World.fold X.env (genesisWorld X name nonce a fs) l = .ok wA)
    {cell : Cell} {rb : ByteArray} {r : Receipt D} {w c₀ : ByteArray} {h₀ : Nat} {rootsB : ByteArray} {s₀ : Nat}
    (hv : Lang.headView (fun b => (dc.decode b).toOption) (X.env.bytes (headPackageId X.env)) cell =
      some (.at w c₀ h₀ rootsB s₀))
    (hro : (dc.decode rootsB).toOption = some (wA.roots X.env))
    (hrb : Receipt.ofBytes X.env dc rb = some r) {h code : Nat} {m : D}
    (hk : Receipt.check X.env h₀ (wA.roots X.env) r.txId 0 r = .ok (.refused h code m)) :
    check X.env dc cell rb = .error "notCommitted" ∧
      (wA.refusalAt X.env (.tx r.txId) = some (.refused h code m) ∨
        CollidesAmong X.env.hash ([rootsPre X.env r.root r.jroot r.rroot r.rowsroot, wA.rootsPre X.env] ++
          inclPres (refusalSpec X.env) (refusalPre X.env) (.refusal (.tx r.txId)) (.refused h code m) r.rpath wA.refusals)) := by
  refine ⟨by simp [check, hv, hro, hrb, hk], ?_⟩
  have h0 : (genesisWorld X name nonce a fs).RefusalsOk X.env :=
    refusalsOk_of_empty (by simp [genesisWorld, World.genesis])
  exact check_refused_sound hE (fold_refusalsOk h0 hA) hk

end Sound

omit [Ord D] in
/-- **P4: a recorded fork checks no receipt.** -/
theorem forked_head_column_refused {E : Env D} {dc : Stream D} {cell : Cell} {rb : ByteArray} {w : ByteArray}
    (hv : Lang.headView (fun b => (dc.decode b).toOption) (E.bytes (headPackageId E)) cell = some (.forked w)) :
    check E dc cell rb = .error "forkedHead" := by
  simp [check, hv]

end Nanodregg.Protocol.Foreign
