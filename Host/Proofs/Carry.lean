/-
# Host.Proofs.Carry — what `host import` accepts, and that what `host export` writes imports (HOST-28)

* `read_ok` — a file `Carry.read` accepts carries this binary's stamp at its head, and its carried
  bytes are exactly the bytes after its head (CODEC's canonical decode: no other spelling reads back);
* `importWorld_ok` — an import accepts exactly what its pin (`Pin.Holds`: the file's digest, or the
  made World's origin), `read` and `world` accept;
* `importWorld_digest` / `read_stamp` / `importWorld_wrongWorld` — the teeth: any other digest is
  refused `digest` before a byte is decoded, any other stamp `shapeMismatch`, and a carry making a
  World of another origin than the pinned one `carryMismatch wrongWorld`, before anything is written;
* `world_carried` — the World an import makes holds the file's carried state, its trie re-authored
  and its window trie cut to the meter (KERNEL's `carry_carried`, KERNEL-79), at the file's anchor
  height;
* `statedAuthority_none`, `importWorld_unstated` — an import that states no authority bears
  `Authority.none`, and only where the carried World's own authority is `Authority.none`; under a
  carried World that certifies it is refused `usage authorityUnstated` before anything is written
  (HOST-82: an operator never drops a World's certifiers by omission);
* `importWorld_sound` — what an import makes is KERNEL's `carry_sound` World: the stated authority
  is the one it bears, and every cell, tombstone, row and meter leaf of the file is its own;
* `exportFile_reads` — a file `export` writes reads back, under the digest it prints, to the
  exported World's carried bytes and height;
* `exportFile_ok` — and export refuses no World whose carried state fits the codec (completeness:
  the export check is not a refusal of good Stores).
-/
import Host.Carry
import Codec.Proofs.Carried
import Codec.Proofs.Raw
import Kernel.Proofs.CarrySound

namespace Nanodregg.Host.Carry

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Stream Nanodregg.Codec.Kernel

theorem head_lawfulOn {D : Type} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun h : Head D => PD h.fromOrigin ∧ h.height < 2 ^ 64 ∧ PD h.chain) (head dc) := by
  have h := refine_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd)) "host/carried-head"
    (accept := fun (o, h, c) => some (⟨o, h, c⟩ : Head D)) (back := fun x => (x.fromOrigin, x.height, x.chain))
    (fun _ _ => rfl) (fun x y hxy => by obtain ⟨a, b, c⟩ := x; cases hxy; rfl)
  exact h.mono (fun _ hv => hv) (fun _ hv => hv)

variable {D : Type} [Ord D] [DecidableEq D]

theorem read_ok [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {f : ByteArray} {r : Read D} (h : read E dc f = .ok r) :
    f.extract 0 stampBytes = (stamp E dc).bytes ∧
      f.extract stampBytes r.carriedAt = (head dc).bytes r.head ∧
      f.extract r.carriedAt f.size = (carried E dc).bytes r.carried ∧
      r.head.height = r.carried.height := by
  unfold read at h
  split at h
  · cases h
  rename_i hst
  split at h
  · cases h
  rename_i x j hget
  split at h
  · cases h
  rename_i c hc
  split at h
  · cases h
  rename_i hh
  cases h
  obtain ⟨_, hj, ho⟩ := (head_lawfulOn hd).occurs_of_get hget
  refine ⟨by simpa using hst, ?_, eq_bytes_of_carried_decode hd hc, by simpa using hh⟩
  rw [hj]; exact ho.2

/-- A file `read` accepts decoded its carried state from its tail (CODEC's carried codec). -/
theorem read_decoded {E : Env D} {dc : Stream D} {f : ByteArray} {r : Read D} (h : read E dc f = .ok r) :
    ∃ b, (carried E dc).decode b = .ok r.carried := by
  unfold read at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i c hc
  split at h
  · cases h
  cases h
  exact ⟨_, hc⟩

theorem read_stamp (E : Env D) (dc : Stream D) {f : ByteArray} (h : f.extract 0 stampBytes ≠ (stamp E dc).bytes) :
    read E dc f = .error (.stamp (f.extract 0 stampBytes)) := by
  unfold read; rw [if_pos h]

/-- What an import's pin demands of its file and the World it makes. -/
def Pin.Holds : Pin D → ByteArray → World D → Prop
  | .digest want, f, _ => digestOf f = want
  | .origin o, _, w => w.origin = o

/-- **Tooth: a digest pin refuses any other file** `carryMismatch digest`, before a byte is read. -/
theorem importWorld_digest (X : Receive.Ctx D) (dc : Stream D) (name nonce : ByteArray) {want : Digest}
    (stated : Option Receive.Authority) {f : ByteArray} (h : digestOf f ≠ want) :
    importWorld X dc name nonce (.digest want) stated f = .error (.carryMismatch, "carryMismatch digest") := by
  unfold importWorld; simp only [if_pos h]; rfl

/-- **Tooth: an origin pin refuses a World of another origin** `carryMismatch wrongWorld`: the file
reads and KERNEL's carry makes `w`, and still nothing is imported (`import --origin`, card 7a). -/
theorem importWorld_wrongWorld {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray} {o : D}
    {stated : Option Receive.Authority} {auth : Receive.Authority}
    {f : ByteArray} {r : Read D} {w : World D} (hr : read X.env dc f = .ok r)
    (ha : statedAuthority r.carried stated = .ok auth)
    (hw : world X name nonce auth r = .ok w) (ho : w.origin ≠ o) :
    importWorld X dc name nonce (.origin o) stated f = .error (.carryMismatch, "carryMismatch wrongWorld") := by
  unfold importWorld carryFile
  rw [hr]
  simp only [ha, hw, ho, decide_false, Bool.false_eq_true, if_false]
  rfl

omit [DecidableEq D] in
/-- **A stated authority is the one the carry takes.** -/
theorem statedAuthority_some (c : Carried D) (a : Receive.Authority) : statedAuthority c (some a) = .ok a := rfl

omit [DecidableEq D] in
/-- **Stated nothing, an import bears `Authority.none`, and only under a carried World whose own
authority is `Authority.none`** (KERNEL-79): nothing is inherited, and no certifier is dropped by
omission. -/
theorem statedAuthority_none {c : Carried D} {a : Receive.Authority} (h : statedAuthority c none = .ok a) :
    a = Receive.Authority.none ∧ Receive.authorityIn c.trie = some Receive.Authority.none := by
  simp only [statedAuthority] at h
  by_cases hc : Receive.authorityIn c.trie = some Receive.Authority.none
  · rw [if_pos hc] at h
    cases h
    exact ⟨rfl, hc⟩
  · rw [if_neg hc] at h
    cases h

/-- **Tooth: an import that states no authority under a certifying World is refused**
`usage authorityUnstated`, by name, after the file reads and before KERNEL's carry or anything is
written (the plant `carry-import-authority-unstated` drives it through `host import`). -/
theorem carryFile_unstated {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray} {f : ByteArray}
    {accept : World D → Bool} {r : Read D} (hr : read X.env dc f = .ok r)
    (hc : Receive.authorityIn r.carried.trie ≠ some Receive.Authority.none) :
    carryFile X dc name nonce none f accept = .error (.usage, "authorityUnstated") := by
  unfold carryFile
  rw [hr]
  simp only [statedAuthority, hc, if_false]
  rfl

theorem importWorld_unstated {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray} {pin : Pin D}
    {f : ByteArray} {r : Read D} (hp : ∀ want, pin = .digest want → digestOf f = want)
    (hr : read X.env dc f = .ok r)
    (hc : Receive.authorityIn r.carried.trie ≠ some Receive.Authority.none) :
    importWorld X dc name nonce pin none f = .error (.usage, "authorityUnstated") := by
  unfold importWorld
  cases pin with
  | digest want =>
    simp only [hp want rfl, ne_eq, not_true_eq_false, if_false]
    exact carryFile_unstated hr hc
  | origin o => exact carryFile_unstated hr hc

/-- **An import holds the file's carried state**, its trie re-authored and its window trie cut to the
meter (KERNEL-79), at the file's anchor height; the file's carried bytes are exactly that state's. -/
theorem world_carried [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {X : Receive.Ctx D} {name nonce : ByteArray} {auth : Receive.Authority} {f : ByteArray}
    {r : Read D} {w₀ : World D}
    (hr : read E dc f = .ok r) (hw : world X name nonce auth r = .ok w₀) :
    (carried E dc).bytes r.carried = f.extract r.carriedAt f.size ∧
      w₀.carried =
        { r.carried with trie := Receive.reauthor X r.carried.trie auth, refusals := Receive.meterOnly X.env r.carried.refusals } ∧
      w₀.height = r.head.height := by
  obtain ⟨_, _, hb, hh⟩ := read_ok hd hr
  have hc := Receive.carry_carried hw
  refine ⟨hb.symm, hc, ?_⟩
  have : w₀.height = w₀.carried.height := rfl
  rw [this, hc, hh]

theorem exportCheck_reads [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {dc : Stream D} {w : World D}
    {f f' : ByteArray} (h : exportCheck E dc w f = .ok f') :
    f' = f ∧ ∃ r, read E dc f = .ok r ∧
      (carried E dc).bytes r.carried = (carried E dc).bytes w.carried ∧
      r.head = ⟨w.origin, w.height, w.chain⟩ := by
  unfold exportCheck at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · rename_i hok
      cases h
      obtain ⟨hb, ho, hh, hc⟩ := hok
      refine ⟨rfl, r, hr, hb, ?_⟩
      rw [← ho, ← hh, ← hc]
    · cases h

theorem carryFile_ok {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray}
    {stated : Option Receive.Authority} {f : ByteArray} {accept : World D → Bool} {w : World D} {r : Read D}
    (h : carryFile X dc name nonce stated f accept = .ok (w, r)) :
    read X.env dc f = .ok r ∧ ∃ auth, statedAuthority r.carried stated = .ok auth ∧
      world X name nonce auth r = .ok w ∧ accept w = true := by
  unfold carryFile at h
  split at h
  · cases h
  · cases h
  · rename_i r' hr
    split at h
    · cases h
    · rename_i auth hauth
      split at h
      · rename_i w' hw
        split at h
        · rename_i ha
          cases h
          exact ⟨hr, auth, hauth, hw, ha⟩
        · cases h
      all_goals cases h

/-- `importWorld` accepts only what its pin, `read` and `world` accept. -/
theorem importWorld_ok {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray} {pin : Pin D}
    {stated : Option Receive.Authority} {f : ByteArray} {w : World D} {r : Read D}
    (h : importWorld X dc name nonce pin stated f = .ok (w, r)) :
    read X.env dc f = .ok r ∧ (∃ auth, statedAuthority r.carried stated = .ok auth ∧
      world X name nonce auth r = .ok w) ∧ pin.Holds f w := by
  unfold importWorld at h
  cases pin with
  | digest want =>
    simp only at h
    split at h
    · cases h
    · rename_i hd
      obtain ⟨hr, auth, ha, hw, -⟩ := carryFile_ok h
      exact ⟨hr, ⟨auth, ha, hw⟩, by simpa [Pin.Holds] using hd⟩
  | origin o =>
    obtain ⟨hr, auth, ha, hw, hacc⟩ := carryFile_ok h
    exact ⟨hr, ⟨auth, ha, hw⟩, by simpa [Pin.Holds] using hacc⟩

/-- **What an import makes is a sound carry** (KERNEL-79, at the host): the authority the World
bears is the one the operator stated (stated nothing: `Authority.none`, under a carried World that
certified nobody), checked by genesis's own `checkAuthority`; every entry of the file's carried
trie but a live authority cell (every cell, tombstone, spent nullifier) is the World's, and nothing
else is; its rows, journal, allowance and height are the file's; its meter is the file's, leaf for
leaf, and it holds no refusal record; every World an honest fold reaches from it bears the same
authority. -/
theorem importWorld_sound [Std.TransOrd D] [Std.LawfulEqOrd D] {PD : D → Prop} {X : Receive.Ctx D} {dc : Stream D}
    (hd : LawfulOn PD dc) {name nonce : ByteArray} {pin : Pin D} {stated : Option Receive.Authority}
    {f : ByteArray} {w : World D} {r : Read D}
    (h : importWorld X dc name nonce pin stated f = .ok (w, r)) :
    ∃ auth, (stated = some auth ∨ (stated = none ∧ auth = Receive.Authority.none ∧
        Receive.authorityIn r.carried.trie = some Receive.Authority.none)) ∧
      Receive.checkAuthority auth = .ok () ∧ Receive.authorityOf w = some auth ∧
      (∀ s l, r.carried.trie.get (trieSpec X.env) s = some l → Receive.liveAuthority s l = false →
        w.trie.get (trieSpec X.env) s = some l) ∧
      (∀ s l, w.trie.get (trieSpec X.env) s = some l →
        r.carried.trie.get (trieSpec X.env) s = some l ∨
          (s = .cell (Receive.authorityId X auth) ∧ l = .entry (.live (Receive.authorityCell auth) 0))) ∧
      w.rows = r.carried.rows ∧ w.journal = r.carried.journal ∧ w.allowance = r.carried.allowance ∧
      w.height = r.carried.height ∧
      (∀ k : MeterSlot D, w.refusals.get (refusalSpec X.env) (.meter k) =
        r.carried.refusals.get (refusalSpec X.env) (.meter k)) ∧
      (∀ k : RefusalSlot D, w.refusalAt X.env k = none) ∧
      (∀ {w' : World D} {l : List (Step D)}, World.fold X.env w l = .ok w' → Receive.Honest X w l →
        Receive.authorityOf w' = some auth) := by
  obtain ⟨hr, ⟨auth, ha, hw⟩, -⟩ := importWorld_ok h
  obtain ⟨_, hdec⟩ := read_decoded hr
  have hcn := (carried_decode_canon hd hdec).1
  have hsl : ∀ s l, r.carried.trie.get (trieSpec X.env) s = some l → Leaf.fits s l = true :=
    fun s l hg => (carried_decode_canon hd hdec).2 (s, l)
      ((Trie.mem_toList (trieSpec X.env) 0 _ hcn.1 s l).mpr hg)
  obtain ⟨hca, -, -, hao, -, -, hk, ho, hrows, hj, hal, hh, -⟩ := Receive.carry_sound hcn hsl hw
  obtain ⟨hm, hn, -⟩ := Receive.carry_meter (carried_decode_window hd hdec).1 hw
  refine ⟨auth, ?_, hca, hao, hk, ho, hrows, hj, hal, hh, hm, hn,
    fun hf hhon => Receive.authorityOf_honest_fold_carry hcn hsl hw hf hhon⟩
  cases stated with
  | some a => exact .inl (by cases ha; rfl)
  | none =>
    obtain ⟨rfl, hn'⟩ := statedAuthority_none ha
    exact .inr ⟨rfl, rfl, hn'⟩

/-- **What export writes, import reads back**: the exported World's carried bytes and its head
(origin, the lineage `import` commits in the new origin; height and chain, the anchor), under the
digest export prints. -/
theorem exportFile_reads [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {dc : Stream D} {w : World D}
    {f : ByteArray} (h : exportFile E dc w = .ok f) :
    ∃ r, read E dc f = .ok r ∧ (carried E dc).bytes r.carried = (carried E dc).bytes w.carried ∧
      r.head = ⟨w.origin, w.height, w.chain⟩ := by
  obtain ⟨rfl, hr⟩ := exportCheck_reads h
  exact hr

/-- **Export refuses no fitting World** (completeness). At Deployed, `Host.Deployed.openWith_exportFile_ok`
proves every part of `hfit` for every World the deployed open returns except its allowance below
2^64: that is its ONE named premise, waiting on cv 01a14ba9-cbf4 (KERNEL must bound weight +
allowance below 2^64), and reachable through `host import` until then. Soundness does not rest on it: export re-reads its file (`exportCheck`) and refuses rather than
write a bad one. -/
theorem exportFile_ok [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {w : World D}
    (hfit : Carried.CodecFits E PD w.carried) (ho : PD w.origin) (hc : PD w.chain) (hh : w.height < 2 ^ 64) :
    exportFile E dc w = .ok (file E dc w) := by
  have hst : (stamp E dc).bytes.size = stampBytes := (stamp E dc).size_eq
  generalize hS : (stamp E dc).bytes = S at hst
  have hf : file E dc w = S ++ ((head dc).bytes ⟨w.origin, w.height, w.chain⟩ ++ (carried E dc).bytes w.carried) := by
    simp [file, hS, ByteArray.append_assoc]
  generalize hH : (head dc).bytes ⟨w.origin, w.height, w.chain⟩ = H at hf
  generalize hC : (carried E dc).bytes w.carried = C at hf
  have hocc : OccursAt (file E dc w) stampBytes ((head dc).bytes ⟨w.origin, w.height, w.chain⟩) := by
    rw [hf, hH]
    refine ⟨by simp [ByteArray.size_append]; omega, ?_⟩
    have e := ByteArray.extract_append_size_add' (a := S) (b := H ++ C) (i := 0) (j := H.size) hst.symm
    simp only [Nat.add_zero] at e
    rw [e, ByteArray.extract_append_eq_left rfl]
  have hget := (head_lawfulOn hd).get_of_occurs ⟨w.origin, w.height, w.chain⟩ (file E dc w) stampBytes
    ⟨ho, hh, hc⟩ hocc
  rw [hH] at hget
  have htail : (file E dc w).extract (stampBytes + H.size) (file E dc w).size = C := by
    rw [hf, ← ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_right (by simp [ByteArray.size_append, hst])
      (by simp [ByteArray.size_append, hst])
  have hdec := (carried_decode_iff hd hfit).mpr hC.symm
  have hst' : (file E dc w).extract 0 stampBytes = (stamp E dc).bytes := by
    rw [hf, hS, ← hst]; exact ByteArray.extract_append_eq_left rfl
  have hread : read E dc (file E dc w) =
      .ok ⟨⟨w.origin, w.height, w.chain⟩, w.carried, stampBytes + H.size⟩ := by
    unfold read
    rw [if_neg (by simp [hst']), hget]
    dsimp only
    rw [htail, hdec]
    dsimp only
    rw [if_neg (by simp [World.carried])]
  unfold exportFile exportCheck
  rw [hread]
  dsimp only
  rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]

end Nanodregg.Host.Carry
