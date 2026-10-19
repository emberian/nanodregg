/-
# Hosting.Proofs.ResidentVolume — what the volume holds across a crash (HOSTING-37)

Over the contract `Resident.Volume` (a crash may bring each entry back as ANY value it held since
the last directory sync, and an unsynced file with ANY contents), and over exactly the steps `keep`
and `forget` perform (`keepOps`, `forgetOps`):
- `keep_durable`: once every step ran, EVERY crash outcome holds exactly the text at the kept name.
- `keep_atomic`: a crash after ANY prefix of the steps comes back, in EVERY outcome, with the old
  kept text or the new one: never another, never a torn file, never nothing where there was a text.
- `keep_live_atomic`: without a crash, a keep stopped after any prefix leaves the old or the new.
- `forget_durable`, `forget_atomic`: likewise (the old text, or nothing).
- `seed_after_keep`, `seed_during_keep`, `seed_after_forget`: what `run`'s first tick starts from
  after such a crash.
- The premises are invariants, not hopes: `Fresh` and `Live` hold of the empty volume and are kept
  by every step and every crash (`fresh_*`, `live_*`); `Stable` (the kept entry and its file
  durable) holds after every crash, every completed keep and every completed forget (`stable_*`).
Teeth: `keep_without_sync_tears` (no file `fsync`: some crash outcome holds an unreadable kept
file), `keep_without_syncDir_reverts` (no directory sync: some crash outcome reverts to the old
text), `in_place_loses_both` (writing the kept name in place: some crash outcome is neither text).

What is code, not theorem: `perform` makes each step its one POSIX call (six arms); `keep` reports
`true` only after `performAll` returned and the read-back matched; that the filesystem meets the
contract is the operator's (a local POSIX filesystem; on Darwin Host.File's sync is F_FULLFSYNC).
A keep or forget that FAILS part way without a crash (the rename or the unlink done, the
directory sync thrown) ends the resident `volume`; its restart runs `resumeOps` before its first
tick (HOSTING-39): a whole keep of what the volume holds, again from its first step (absent: a whole
forget). `resume_durable`: every crash outcome after it reads exactly what the start read, for ANY
readable volume; `stable_after_resume`: it re-establishes `Stable`; `keep_resumed`,
`forget_resumed`: after a keep (forget) stopped at any prefix and the resume, every crash outcome is
as after one completed keep (forget), or as before it began; `next_keep_after_resume`,
`next_forget_after_resume`: a crash at every prefix of the next keep (forget) comes back with what
the start read or the new text (nothing). So a text the new life acts on is never undone by a
crash. `resume_atomic`: the resume itself may fail or crash at any prefix, any number of lives in a
row: under `KeptSynced` (every inode the kept name has held since the last directory sync is synced
and readable; it holds of the empty volume and is kept by every keep and forget prefix and every
crash, `keptSynced_*`) every outcome is readable again (`readable_of_keptSynced`), so no start is
wedged at an unreadable kept FILE, and no life acts before its resume read back. (That a readable
text also reads as an answer, `keptRead`, is not this model's: every text kept is `keptText`'s, or a
resumed one that already passed `seedOf`.) Teeth:
`unresumed_keep_reverts`, `unresumed_forget_reverts` (without the resume, the start reads the new
text, or nothing, and a crash comes back with the old one).
Code, not theorem, of the resume: `held` (`pathExists`, then `readFile`) is `Vol.read` at the kept
name; `readFile`'s text written back by `keepOps` is the bytes read (the kept text is the resident's
own UTF-8, `keptText`); `resume`'s read-back can see a step that did not happen or another writer,
never durability (by `resume_read` it always matches under the contract).
Assumed of the deployment, not proved: the volume's history is the empty volume followed only by
`keepOps`, `forgetOps` and crashes, i.e. nothing but this resident writes `kept-*` or `kept-*.tmp`
in its volume (the grain's volume is its own: grain-launch's write grant).
-/
import Hosting.Resident.Volume
import Hosting.Proofs.Resident

namespace Nanodregg.Hosting.Proofs.ResidentVolume

open Nanodregg.Hosting Nanodregg.Hosting.Resident

/-- `v'` is a state a crash of `v` may come back as. -/
def Crash (v v' : Vol) : Prop :=
  (∀ p, v'.live p ∈ v.hist p) ∧ (∀ p, v'.hist p = [v'.live p]) ∧
  (∀ i, v.synced i = true → v'.data i = v.data i) ∧ (∀ i, v'.synced i = true) ∧
  v'.next = v.next ∧ v'.cur = none

/-- Every inode an entry has named since the last directory sync is below `next`. -/
def Fresh (v : Vol) : Prop := ∀ p x i, x ∈ v.hist p → x = some i → i < v.next

/-- The live entry is among the remembered values. -/
def Live (v : Vol) : Prop := ∀ p, v.live p ∈ v.hist p

/-- The name is held durably: it has held one value since the last directory sync, and the file
it names (if any) is synced. -/
def Stable (v : Vol) (p : System.FilePath) : Prop :=
  v.hist p = [v.live p] ∧ ∀ i, v.live p = some i → v.synced i = true

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) :
    upd f k v k = v := by simp [upd]

theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) {k x : α} (v : β) (h : x ≠ k) :
    upd f k v x = f x := by simp [upd, h]

/-- The fresh copy is never the kept name. -/
theorem keptTmp_ne (w : Where) : w.keptTmp ≠ w.kept := by
  intro h
  have := congrArg (fun p : System.FilePath => p.toString.length) h
  simp [Where.keptTmp] at this

/-! ## The invariants -/

theorem fresh_empty : Fresh Vol.empty := by
  intro p x i hx he; simp [Vol.empty] at hx; subst hx; simp at he

theorem live_empty : Live Vol.empty := by intro p; simp [Vol.empty]

theorem fresh_set {v : Vol} {p : System.FilePath} {x : Option Nat} (hf : Fresh v)
    (hx : ∀ i, x = some i → i < v.next) : Fresh (v.set p x) := by
  intro q y i hy he
  simp only [Vol.set, upd] at hy ⊢
  split at hy
  · simp at hy; rcases hy with hy | rfl
    · exact hf _ _ _ (by subst_vars; exact hy) he
    · exact hx i he
  · exact hf _ _ _ hy he

theorem live_set {v : Vol} {p : System.FilePath} {x : Option Nat} (hl : Live v) : Live (v.set p x) := by
  intro q; simp only [Vol.set, upd]; split <;> simp_all [hl q]

theorem fresh_apply {v : Vol} (op : FsOp) (hf : Fresh v) (hl : Live v) : Fresh (v.apply op) := by
  cases op with
  | removeIfExists p => exact fresh_set hf (by simp)
  | create p =>
    intro q y i hy he
    simp only [Vol.apply, Vol.set, upd] at hy ⊢
    split at hy
    · rename_i hq; subst hq
      rcases List.mem_append.mp hy with hy | hy
      · exact Nat.lt_succ_of_lt (hf _ _ _ hy he)
      · simp at hy; subst hy; simp at he; omega
    · exact Nat.lt_succ_of_lt (hf _ _ _ hy he)
  | write s => simp only [Vol.apply]; split <;> exact hf
  | sync => simp only [Vol.apply]; split <;> exact hf
  | rename a b =>
    simp only [Vol.apply]
    refine fresh_set (fresh_set hf ?_) (by simp)
    intro i hi; exact hf a _ i (hl a) hi
  | syncDir d =>
    intro q y i hy he
    simp only [Vol.apply, List.mem_singleton] at hy
    exact hf q _ i (hl q) (hy ▸ he)

theorem live_apply {v : Vol} (op : FsOp) (hl : Live v) : Live (v.apply op) := by
  cases op with
  | removeIfExists p => exact live_set hl
  | create p => intro q; simp only [Vol.apply]; exact live_set hl q
  | write s => simp only [Vol.apply]; split <;> exact hl
  | sync => simp only [Vol.apply]; split <;> exact hl
  | rename a b => exact live_set (live_set hl)
  | syncDir d => intro q; simp [Vol.apply]

theorem fresh_applyAll {v : Vol} (ops : List FsOp) (hf : Fresh v) (hl : Live v) :
    Fresh (v.applyAll ops) ∧ Live (v.applyAll ops) := by
  induction ops generalizing v with
  | nil => exact ⟨hf, hl⟩
  | cons op ops ih => exact ih (fresh_apply op hf hl) (live_apply op hl)

theorem fresh_crash {v v' : Vol} (hc : Crash v v') (hf : Fresh v) : Fresh v' := by
  obtain ⟨hl, hh, -, -, hn, -⟩ := hc
  intro p x i hx he
  rw [hh p, List.mem_singleton] at hx
  subst hx
  rw [hn]; exact hf p _ i (hl p) he

theorem live_crash {v v' : Vol} (hc : Crash v v') : Live v' := by
  intro p; rw [hc.2.1 p]; simp

/-- After a crash every name is held durably. -/
theorem stable_crash {v v' : Vol} (hc : Crash v v') (p : System.FilePath) : Stable v' p :=
  ⟨hc.2.1 p, fun i _ => hc.2.2.2.1 i⟩

/-! ## Keep -/

theorem keep_hist (v : Vol) (w : Where) (s : String) (n : Nat) :
    (v.applyAll ((keepOps w s).take n)).hist w.kept =
      if n ≤ 4 then v.hist w.kept else if n = 5 then v.hist w.kept ++ [some v.next]
      else [some v.next] := by
  have hne := keptTmp_ne w
  rcases n with _ | _ | _ | _ | _ | _ | n <;>
    simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, upd, hne, hne.symm]

theorem keep_inode (v : Vol) (w : Where) (s : String) (n : Nat) (i : Nat) (hi : i < v.next) :
    (v.applyAll ((keepOps w s).take n)).data i = v.data i ∧
    (v.applyAll ((keepOps w s).take n)).synced i = v.synced i := by
  have hne := keptTmp_ne w
  have h := Nat.ne_of_lt hi
  rcases n with _ | _ | _ | _ | _ | _ | n <;>
    simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, upd, h]

theorem keep_new (v : Vol) (w : Where) (s : String) (n : Nat) (hn : 5 ≤ n) :
    (v.applyAll ((keepOps w s).take n)).data v.next = some s ∧
    (v.applyAll ((keepOps w s).take n)).synced v.next = true := by
  rcases n with _ | _ | _ | _ | _ | _ | n
  all_goals first | omega | simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, upd]

/-- **A keep is atomic across a crash**: after any prefix of its steps, every crash outcome holds
the old kept text or the new one at the kept name. -/
theorem keep_atomic (v : Vol) (w : Where) (s : String) (hs : Stable v w.kept) (hf : Fresh v)
    (hl : Live v) (n : Nat) (v' : Vol) (hc : Crash (v.applyAll ((keepOps w s).take n)) v') :
    v'.read w.kept = v.read w.kept ∨ v'.read w.kept = some (some s) := by
  obtain ⟨hcl, -, hcd, -, -, -⟩ := hc
  have hm := hcl w.kept
  rw [keep_hist, hs.1] at hm
  have hold : v'.live w.kept = v.live w.kept → v'.read w.kept = v.read w.kept := by
    intro he
    simp only [Vol.read, he]
    cases hk : v.live w.kept with
    | none => rfl
    | some i =>
      have hi : i < v.next := hf w.kept _ i (hl w.kept) hk
      obtain ⟨hd, hsy⟩ := keep_inode v w s n i hi
      simp only [Option.map_some]
      rw [hcd i (by rw [hsy]; exact hs.2 i hk), hd]
  have hnew : 5 ≤ n → v'.live w.kept = some v.next → v'.read w.kept = some (some s) := by
    intro hn he
    obtain ⟨hd, hsy⟩ := keep_new v w s n hn
    simp only [Vol.read, he, Option.map_some]
    rw [hcd _ hsy, hd]
  split at hm
  · exact .inl (hold (by simpa using hm))
  · split at hm
    · rename_i h4 h5
      simp at hm
      rcases hm with hm | hm
      · exact .inl (hold hm)
      · exact .inr (hnew (by omega) hm)
    · rename_i h4 h5
      simp at hm
      exact .inr (hnew (by omega) hm)

/-- **A completed keep is durable**: every crash outcome holds exactly the text. -/
theorem keep_durable (v : Vol) (w : Where) (s : String) (v' : Vol)
    (hc : Crash (v.applyAll (keepOps w s)) v') : v'.read w.kept = some (some s) := by
  obtain ⟨hcl, -, hcd, -, -, -⟩ := hc
  have hm := hcl w.kept
  have h6 : (keepOps w s).take 6 = keepOps w s := rfl
  have hk := keep_hist v w s 6
  have hn := keep_new v w s 6 (by omega)
  rw [h6] at hk hn
  rw [hk] at hm
  simp at hm
  simp only [Vol.read, hm, Option.map_some]
  rw [hcd _ hn.2, hn.1]

/-- Without a crash, a keep stopped after any prefix leaves the old text or the new. -/
theorem keep_live_atomic (v : Vol) (w : Where) (s : String) (hf : Fresh v) (hl : Live v) (n : Nat) :
    (v.applyAll ((keepOps w s).take n)).read w.kept = v.read w.kept ∨
    (v.applyAll ((keepOps w s).take n)).read w.kept = some (some s) := by
  have hne := keptTmp_ne w
  have hold : ∀ v'' : Vol, v''.live w.kept = v.live w.kept →
      (∀ i, i < v.next → v''.data i = v.data i) → v''.read w.kept = v.read w.kept := by
    intro v'' he hd
    simp only [Vol.read, he]
    cases hk : v.live w.kept with
    | none => rfl
    | some i => simp only [Option.map_some]; rw [hd i (hf w.kept _ i (hl w.kept) hk)]
  rcases n with _ | _ | _ | _ | _ | _ | n
  all_goals first
    | (left; apply hold
       · simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, upd, hne, hne.symm]
       · intro i hi; simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, upd, Nat.ne_of_lt hi])
    | (right; simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, Vol.read, upd, hne, hne.symm])

theorem stable_after_keep (v : Vol) (w : Where) (s : String) :
    Stable (v.applyAll (keepOps w s)) w.kept := by
  have hne := keptTmp_ne w
  constructor
  · simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, upd, hne, hne.symm]
  · intro i hi
    simp [keepOps, Vol.applyAll, Vol.apply, Vol.set, upd, hne, hne.symm] at hi ⊢
    subst hi; simp

/-! ## Forget -/

theorem forget_atomic (v : Vol) (w : Where) (hs : Stable v w.kept) (n : Nat) (v' : Vol)
    (hc : Crash (v.applyAll ((forgetOps w).take n)) v') :
    v'.read w.kept = v.read w.kept ∨ v'.read w.kept = none := by
  obtain ⟨hcl, -, hcd, -, -, -⟩ := hc
  have hm := hcl w.kept
  have hold : v'.live w.kept = v.live w.kept → (∀ i, v.synced i = true →
      (v.applyAll ((forgetOps w).take n)).synced i = true ∧
      (v.applyAll ((forgetOps w).take n)).data i = v.data i) →
      v'.read w.kept = v.read w.kept := by
    intro he hd
    simp only [Vol.read, he]
    cases hk : v.live w.kept with
    | none => rfl
    | some i =>
      obtain ⟨h1, h2⟩ := hd i (hs.2 i hk)
      simp only [Option.map_some]; rw [hcd i h1, h2]
  have hsame : ∀ i, v.synced i = true → (v.applyAll ((forgetOps w).take n)).synced i = true ∧
      (v.applyAll ((forgetOps w).take n)).data i = v.data i := by
    intro i hi
    rcases n with _ | _ | n <;> simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, hi]
  rcases n with _ | _ | n
  · simp [forgetOps, Vol.applyAll, hs.1] at hm
    exact .inl (hold hm hsame)
  · simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd, hs.1] at hm
    rcases hm with hm | hm
    · exact .inl (hold hm hsame)
    · exact .inr (by simp [Vol.read, hm])
  · simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd] at hm
    exact .inr (by simp [Vol.read, hm])

theorem forget_durable (v : Vol) (w : Where) (v' : Vol) (hc : Crash (v.applyAll (forgetOps w)) v') :
    v'.read w.kept = none := by
  have hm := hc.1 w.kept
  simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd] at hm
  simp [Vol.read, hm]

theorem stable_after_forget (v : Vol) (w : Where) : Stable (v.applyAll (forgetOps w)) w.kept := by
  constructor
  · simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd]
  · intro i hi; simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd] at hi

/-! ## The seed -/

/-- After a completed keep whose read-back reported `(r, t)`, every crash restarts with `(r, t)`. -/
theorem seed_after_keep (v : Vol) (w : Where) (s : String) {r : Ring} {t : ByteArray}
    (hb : keptRead s = some (r, t)) (v' : Vol) (hc : Crash (v.applyAll (keepOps w s)) v') :
    seedOf (v'.read w.kept) = some (some (r, t)) := by
  rw [keep_durable v w s v' hc]; simp [seedOf, hb]

/-- A crash at any step of a keep restarts from the old seed or from the keep's answer. -/
theorem seed_during_keep (v : Vol) (w : Where) (s : String) (hs : Stable v w.kept) (hf : Fresh v)
    (hl : Live v) {r : Ring} {t : ByteArray} (hb : keptRead s = some (r, t)) (n : Nat) (v' : Vol)
    (hc : Crash (v.applyAll ((keepOps w s).take n)) v') :
    seedOf (v'.read w.kept) = seedOf (v.read w.kept) ∨ seedOf (v'.read w.kept) = some (some (r, t)) := by
  rcases keep_atomic v w s hs hf hl n v' hc with h | h
  · exact .inl (by rw [h])
  · exact .inr (by rw [h]; simp [seedOf, hb])

/-- After a completed forget, every crash restarts with nothing kept. -/
theorem seed_after_forget (v : Vol) (w : Where) (v' : Vol) (hc : Crash (v.applyAll (forgetOps w)) v') :
    seedOf (v'.read w.kept) = some none := by
  rw [forget_durable v w v' hc]; rfl

/-! ## Teeth: each sync is needed -/

/-- Without the file's `fsync`, a completed keep has a crash outcome whose kept file is
unreadable. -/
theorem keep_without_sync_tears (v : Vol) (w : Where) (s : String) (hf : Fresh v) (hl : Live v) :
    let u := v.applyAll ((keepOps w s).filter fun | .sync => false | _ => true)
    ∃ v', Crash u v' ∧ v'.read w.kept = some none := by
  intro u
  have hne := keptTmp_ne w
  have hlu : Live u := (fresh_applyAll _ hf hl).2
  refine ⟨u.settle u.live (upd u.data v.next none), ⟨hlu, fun p => rfl, ?_, fun _ => rfl, rfl, rfl⟩, ?_⟩
  · intro i hi
    simp only [Vol.settle]
    have : i ≠ v.next := by
      intro he; subst he
      simp [u, keepOps, Vol.applyAll, Vol.apply, Vol.set, upd] at hi
    simp [upd, this]
  · simp [u, Vol.settle, Vol.read, keepOps, Vol.applyAll, Vol.apply, Vol.set, upd, hne, hne.symm]

/-- Without the directory's `fsync` (every step but the last), a crash may revert to the old text:
a keep stopped there has not kept the new one. -/
theorem keep_without_syncDir_reverts (v : Vol) (w : Where) (s : String) (hs : Stable v w.kept)
    (hf : Fresh v) (hl : Live v) (hold : v.read w.kept ≠ some (some s)) :
    let u := v.applyAll ((keepOps w s).take 5)
    ∃ v', Crash u v' ∧ v'.read w.kept ≠ some (some s) := by
  intro u
  have hne := keptTmp_ne w
  have hlu : Live u := (fresh_applyAll _ hf hl).2
  let L := upd u.live w.kept (v.live w.kept)
  refine ⟨u.settle L u.data, ⟨?_, fun p => rfl, fun i _ => rfl, fun _ => rfl, rfl, rfl⟩, ?_⟩
  · intro p
    simp only [Vol.settle, L, upd]
    split
    · subst_vars
      have hk := keep_hist v w s 5
      simp only [show ¬ (5 ≤ 4) from by omega, if_false, if_true] at hk
      show v.live w.kept ∈ u.hist w.kept
      rw [hk, hs.1]; simp
    · exact hlu p
  · intro hn; apply hold; rw [← hn]
    simp only [Vol.settle, Vol.read, L, upd_same]
    cases hk : v.live w.kept with
    | none => rfl
    | some i =>
      simp only [Option.map_some]
      rw [(keep_inode v w s 5 i (hf w.kept _ i (hl w.kept) hk)).1]

/-- Writing the kept name in place (no tmp): after `create`, a directory sync and the write, some
crash outcome holds neither the old text nor the new: the file is unreadable. -/
theorem in_place_loses_both (v : Vol) (w : Where) (s : String) (hf : Fresh v) (hl : Live v) :
    let u := v.applyAll [.removeIfExists w.kept, .create w.kept, .syncDir w.vol, .write s]
    ∃ v', Crash u v' ∧ v'.read w.kept = some none := by
  intro u
  have hlu : Live u := (fresh_applyAll _ hf hl).2
  refine ⟨u.settle u.live (upd u.data v.next none), ⟨hlu, fun p => rfl, ?_, fun _ => rfl, rfl, rfl⟩, ?_⟩
  · intro i hi
    simp only [Vol.settle]
    have : i ≠ v.next := by
      intro he; subst he
      simp [u, Vol.applyAll, Vol.apply, Vol.set, upd] at hi
    simp [upd, this]
  · simp [u, Vol.settle, Vol.read, Vol.applyAll, Vol.apply, Vol.set, upd]

/-! ## The resume (HOSTING-39) -/

theorem live_applyAll {v : Vol} (ops : List FsOp) (hl : Live v) : Live (v.applyAll ops) := by
  induction ops generalizing v with
  | nil => exact hl
  | cons op ops ih => exact ih (live_apply op hl)

/-- Without a crash, the resume leaves the kept name reading as it did. -/
theorem resume_read (v : Vol) (w : Where) :
    (v.applyAll (resumeOps w (v.read w.kept))).read w.kept = v.read w.kept := by
  have hne := keptTmp_ne w
  cases h : v.read w.kept with
  | none =>
    simp [resumeOps, forgetOps, Vol.applyAll, Vol.apply, Vol.set, Vol.read, upd]
  | some x =>
    cases x with
    | none => simp [resumeOps, Vol.applyAll, h]
    | some s =>
      simp [resumeOps, keepOps, Vol.applyAll, Vol.apply, Vol.set, Vol.read, upd, hne, hne.symm]

/-- **The resume is durable, for every volume**: after it, every crash outcome reads exactly what
the start read (an unreadable entry excepted: the start ends `volume` before resuming it). -/
theorem resume_durable (v : Vol) (w : Where) (hu : v.read w.kept ≠ some none) (v' : Vol)
    (hc : Crash (v.applyAll (resumeOps w (v.read w.kept))) v') : v'.read w.kept = v.read w.kept := by
  cases h : v.read w.kept with
  | none => rw [h] at hc; exact forget_durable v w v' hc
  | some x =>
    cases x with
    | none => exact absurd h hu
    | some s => rw [h] at hc; exact keep_durable v w s v' hc

/-- The resume re-establishes `Stable` at the kept name. -/
theorem stable_after_resume (v : Vol) (w : Where) (hu : v.read w.kept ≠ some none) :
    Stable (v.applyAll (resumeOps w (v.read w.kept))) w.kept := by
  cases h : v.read w.kept with
  | none => exact stable_after_forget v w
  | some x =>
    cases x with
    | none => exact absurd h hu
    | some s => exact stable_after_keep v w s

/-- A crash at every prefix of the keep after the resume comes back with what the start read or
the keep's text. -/
theorem next_keep_after_resume (v : Vol) (w : Where) (hu : v.read w.kept ≠ some none)
    (hf : Fresh v) (hl : Live v) (s : String) (m : Nat) (v' : Vol)
    (hc : Crash (((v.applyAll (resumeOps w (v.read w.kept))).applyAll ((keepOps w s).take m))) v') :
    v'.read w.kept = v.read w.kept ∨ v'.read w.kept = some (some s) := by
  obtain ⟨hf2, hl2⟩ := fresh_applyAll (resumeOps w (v.read w.kept)) hf hl
  have h := keep_atomic _ w s (stable_after_resume v w hu) hf2 hl2 m v' hc
  rwa [resume_read] at h

/-- A crash at every prefix of the forget after the resume comes back with what the start read or
nothing. -/
theorem next_forget_after_resume (v : Vol) (w : Where) (hu : v.read w.kept ≠ some none) (m : Nat)
    (v' : Vol) (hc : Crash (((v.applyAll (resumeOps w (v.read w.kept))).applyAll ((forgetOps w).take m))) v') :
    v'.read w.kept = v.read w.kept ∨ v'.read w.kept = none := by
  have h := forget_atomic _ w (stable_after_resume v w hu) m v' hc
  rwa [resume_read] at h

/-- **`keep_resumed`**: a keep of `s` stopped at ANY prefix without a crash (from a readable kept
entry), then the restart's resume: every crash outcome reads what the start read, and that is
the text before the keep or `s`, as after one completed keep or none. -/
theorem keep_resumed (v : Vol) (w : Where) (s : String) (hf : Fresh v) (hl : Live v) (hr : v.read w.kept ≠ some none) (n : Nat) (v' : Vol)
    (hc : Crash (let u := v.applyAll ((keepOps w s).take n); u.applyAll (resumeOps w (u.read w.kept))) v') :
    v'.read w.kept = (v.applyAll ((keepOps w s).take n)).read w.kept ∧
    (v'.read w.kept = v.read w.kept ∨ v'.read w.kept = some (some s)) := by
  have hla := keep_live_atomic v w s hf hl n
  have hu : (v.applyAll ((keepOps w s).take n)).read w.kept ≠ some none := by
    rcases hla with h | h <;> rw [h]
    · exact hr
    · simp
  have hd := resume_durable _ w hu v' hc
  exact ⟨hd, by rw [hd]; exact hla⟩

/-- **`forget_resumed`**: likewise for a forget stopped at any prefix: the text before it, or
nothing. -/
theorem forget_resumed (v : Vol) (w : Where) (hr : v.read w.kept ≠ some none)
    (n : Nat) (v' : Vol)
    (hc : Crash (let u := v.applyAll ((forgetOps w).take n); u.applyAll (resumeOps w (u.read w.kept))) v') :
    v'.read w.kept = (v.applyAll ((forgetOps w).take n)).read w.kept ∧
    (v'.read w.kept = v.read w.kept ∨ v'.read w.kept = none) := by
  have hla : (v.applyAll ((forgetOps w).take n)).read w.kept = v.read w.kept ∨
      (v.applyAll ((forgetOps w).take n)).read w.kept = none := by
    rcases n with _ | _ | n
    · exact .inl rfl
    · exact .inr (by simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, Vol.read, upd])
    · right; simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, Vol.read, upd]
  have hu : (v.applyAll ((forgetOps w).take n)).read w.kept ≠ some none := by
    rcases hla with h | h <;> rw [h]
    · exact hr
    · simp
  have hd := resume_durable _ w hu v' hc
  exact ⟨hd, by rw [hd]; exact hla⟩

/-- Tooth: without the resume, a keep that failed after its rename (before its directory sync)
leaves the start reading the new text, and a crash before anything else comes back with the old
one: the start acted on a text the volume had not kept. -/
theorem unresumed_keep_reverts (v : Vol) (w : Where) (s : String) (hs : Stable v w.kept)
    (hf : Fresh v) (hl : Live v) (hold : v.read w.kept ≠ some (some s)) :
    let u := v.applyAll ((keepOps w s).take 5)
    u.read w.kept = some (some s) ∧ ∃ v', Crash u v' ∧ v'.read w.kept ≠ u.read w.kept := by
  intro u
  have hne := keptTmp_ne w
  have hu : u.read w.kept = some (some s) := by
    simp [u, keepOps, Vol.applyAll, Vol.apply, Vol.set, Vol.read, upd, hne, hne.symm]
  obtain ⟨v', hc, hv⟩ := keep_without_syncDir_reverts v w s hs hf hl hold
  exact ⟨hu, v', hc, hu ▸ hv⟩

/-- Tooth: without the resume, a forget that failed after its unlink leaves the start reading
nothing, and a crash comes back with the forgotten text. -/
theorem unresumed_forget_reverts (v : Vol) (w : Where) (hs : Stable v w.kept) (hl : Live v)
    (hold : v.read w.kept ≠ none) :
    let u := v.applyAll ((forgetOps w).take 1)
    u.read w.kept = none ∧ ∃ v', Crash u v' ∧ v'.read w.kept ≠ u.read w.kept := by
  intro u
  have hlu : Live u := live_applyAll ((forgetOps w).take 1) hl
  have hu : u.read w.kept = none := by
    simp [u, forgetOps, Vol.applyAll, Vol.apply, Vol.set, Vol.read, upd]
  let L := upd u.live w.kept (v.live w.kept)
  refine ⟨hu, u.settle L u.data, ⟨?_, fun p => rfl, fun i _ => rfl, fun _ => rfl, rfl, rfl⟩, ?_⟩
  · intro p
    simp only [Vol.settle, L, upd]
    split
    · subst_vars
      show v.live w.kept ∈ u.hist w.kept
      simp [u, forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd, hs.1]
    · exact hlu p
  · rw [hu]
    have hd : u.data = v.data := by simp [u, forgetOps, Vol.applyAll, Vol.apply, Vol.set]
    simp only [Vol.settle, Vol.read, L, upd_same, hd]
    simpa [Vol.read] using hold

/-! ## Every life stays readable (HOSTING-39): the resume itself may fail or crash -/

/-- Every inode the kept name has named since the last directory sync is synced and readable. -/
def KeptSynced (v : Vol) (w : Where) : Prop :=
  ∀ x ∈ v.hist w.kept, ∀ i, x = some i → v.synced i = true ∧ ∃ s, v.data i = some s

theorem keptSynced_empty (w : Where) : KeptSynced Vol.empty w := by
  intro x hx i he; simp [Vol.empty] at hx; subst hx; simp at he

/-- A readable kept name: under `KeptSynced` the start never meets an unreadable kept file. -/
theorem readable_of_keptSynced {v : Vol} {w : Where} (hk : KeptSynced v w) (hl : Live v) :
    v.read w.kept ≠ some none := by
  cases h : v.live w.kept with
  | none => simp [Vol.read, h]
  | some i =>
    obtain ⟨-, s, hs⟩ := hk _ (h ▸ hl w.kept) i rfl
    simp [Vol.read, h, hs]

theorem keptSynced_keep (v : Vol) (w : Where) (s : String) (hk : KeptSynced v w) (hf : Fresh v)
    (n : Nat) : KeptSynced (v.applyAll ((keepOps w s).take n)) w := by
  intro x hx i he
  rw [keep_hist] at hx
  have hold : x ∈ v.hist w.kept → (v.applyAll ((keepOps w s).take n)).synced i = true ∧
      ∃ t, (v.applyAll ((keepOps w s).take n)).data i = some t := by
    intro hx'
    obtain ⟨h1, t, h2⟩ := hk x hx' i he
    obtain ⟨hd, hsy⟩ := keep_inode v w s n i (hf w.kept x i hx' he)
    exact ⟨by rw [hsy]; exact h1, t, by rw [hd]; exact h2⟩
  have hnew : 5 ≤ n → i = v.next → (v.applyAll ((keepOps w s).take n)).synced i = true ∧
      ∃ t, (v.applyAll ((keepOps w s).take n)).data i = some t := by
    intro hn hi; subst hi
    obtain ⟨hd, hsy⟩ := keep_new v w s n hn
    exact ⟨hsy, s, hd⟩
  split at hx
  · exact hold hx
  · split at hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hold hx
      · simp at hx; subst hx; exact hnew (by omega) (by simpa using he.symm)
    · simp at hx; subst hx; exact hnew (by omega) (by simpa using he.symm)

theorem keptSynced_forget (v : Vol) (w : Where) (hk : KeptSynced v w) (n : Nat) :
    KeptSynced (v.applyAll ((forgetOps w).take n)) w := by
  intro x hx i he
  have hsame : (v.applyAll ((forgetOps w).take n)).synced = v.synced ∧
      (v.applyAll ((forgetOps w).take n)).data = v.data := by
    rcases n with _ | _ | n <;> simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set]
  rw [hsame.1, hsame.2]
  rcases n with _ | _ | n
  · exact hk x (by simpa [Vol.applyAll] using hx) i he
  · simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd] at hx
    rcases hx with hx | hx
    · exact hk x hx i he
    · subst hx; simp at he
  · simp [forgetOps, Vol.applyAll, Vol.apply, Vol.set, upd] at hx
    subst hx; simp at he

theorem keptSynced_crash {v v' : Vol} {w : Where} (hk : KeptSynced v w) (hc : Crash v v') :
    KeptSynced v' w := by
  obtain ⟨hcl, hh, hcd, hcs, -, -⟩ := hc
  intro x hx i he
  rw [hh, List.mem_singleton] at hx
  subst hx
  obtain ⟨h1, s, h2⟩ := hk _ (hcl w.kept) i he
  exact ⟨hcs i, s, (hcd i h1).trans h2⟩

theorem keptSynced_resume (v : Vol) (w : Where) (hk : KeptSynced v w) (hf : Fresh v) (n : Nat) :
    KeptSynced (v.applyAll ((resumeOps w (v.read w.kept)).take n)) w := by
  cases h : v.read w.kept with
  | none => exact keptSynced_forget v w hk n
  | some x =>
    cases x with
    | none => simpa [resumeOps, Vol.applyAll] using hk
    | some s => exact keptSynced_keep v w s hk hf n

/-- **The resume is safe to interrupt**: a crash at ANY prefix of the resume (from a volume every
life has kept `KeptSynced`) comes back readable and `KeptSynced` again, so a resume that fails or
crashes part way, any number of lives in a row, never wedges a later start at an unreadable file;
and no life acted on anything between (each ends before its first tick). -/
theorem resume_atomic (v : Vol) (w : Where) (hk : KeptSynced v w) (hf : Fresh v) (hl : Live v)
    (n : Nat) (v' : Vol)
    (hc : Crash (v.applyAll ((resumeOps w (v.read w.kept)).take n)) v') :
    v'.read w.kept ≠ some none ∧ KeptSynced v' w ∧ Fresh v' ∧ Live v' := by
  have hk' := keptSynced_crash (keptSynced_resume v w hk hf n) hc
  have hl' := live_crash hc
  exact ⟨readable_of_keptSynced hk' hl', hk', fresh_crash hc (fresh_applyAll _ hf hl).1, hl'⟩

end Nanodregg.Hosting.Proofs.ResidentVolume
