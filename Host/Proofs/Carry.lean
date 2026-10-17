/-
# Host.Proofs.Carry — what `host import` accepts, and that what `host export` writes imports (HOST-28)

* `read_ok` — a file `Carry.read` accepts hashes to the operator's digest, carries this binary's
  stamp at its head, and its carried bytes are exactly the bytes after its head (CODEC's canonical
  decode: no other spelling reads back);
* `read_digest` / `read_stamp` — the teeth: any other digest is refused `digest`, any other stamp
  `shapeMismatch`, before a byte is decoded;
* `world_carried` — the World an import makes holds EXACTLY the file's carried bytes (KERNEL's
  `carry_carried`) at the file's anchor height: the reopen compare (`reopen`) is a pair assertion
  on the base codec, never the first check of the contents;
* `exportFile_reads` — a file `export` writes reads back, under the digest it prints, to the
  exported World's carried bytes and height;
* `exportFile_ok` — and export refuses no World whose carried state fits the codec (completeness:
  the export check is not a refusal of good Stores).
-/
import Host.Carry
import Codec.Proofs.Carried
import Codec.Proofs.Raw
import Kernel.Proofs.Carry

namespace Nanodregg.Host.Carry

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Stream Nanodregg.Codec.Kernel

theorem head_lawfulOn {D : Type} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun h : Head D => PD h.fromOrigin ∧ h.height < 2 ^ 64 ∧ PD h.chain) (head dc) := by
  have h := refine_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd)) "host/carried-head"
    (accept := fun (o, h, c) => some (⟨o, h, c⟩ : Head D)) (back := fun x => (x.fromOrigin, x.height, x.chain))
    (fun _ _ => rfl) (fun x y hxy => by obtain ⟨a, b, c⟩ := x; cases hxy; rfl)
  exact h.mono (fun _ hv => hv) (fun _ hv => hv)

variable {D : Type} [Ord D] [DecidableEq D]

theorem read_ok [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {want : Digest}
    {f : ByteArray} {r : Read D} (h : read E dc want f = .ok r) :
    digestOf f = want ∧ f.extract 0 stampBytes = (stamp E dc).bytes ∧
      f.extract stampBytes r.carriedAt = (head dc).bytes r.head ∧
      f.extract r.carriedAt f.size = (carried E dc).bytes r.carried ∧
      r.head.height = r.carried.height := by
  unfold read at h
  split at h
  · cases h
  rename_i hdg
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
  refine ⟨by simpa using hdg, by simpa using hst, ?_, eq_bytes_of_carried_decode hd hc, by simpa using hh⟩
  rw [hj]; exact ho.2

theorem read_digest (E : Env D) (dc : Stream D) {want : Digest} {f : ByteArray} (h : digestOf f ≠ want) :
    read E dc want f = .error .digest := by
  unfold read; rw [if_pos h]

theorem read_stamp (E : Env D) (dc : Stream D) {f : ByteArray} (h : f.extract 0 stampBytes ≠ (stamp E dc).bytes) :
    read E dc (digestOf f) f = .error (.stamp (f.extract 0 stampBytes)) := by
  unfold read; rw [if_neg (by simp), if_pos h]

/-- **An import holds exactly the file's carried bytes**, at the file's anchor height. -/
theorem world_carried [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {X : Receive.Ctx D} {name nonce : ByteArray} {want : Digest} {f : ByteArray}
    {r : Read D} {w₀ : World D}
    (hr : read E dc want f = .ok r) (hw : world X name nonce r = .ok w₀) :
    digestOf f = want ∧ (carried E dc).bytes w₀.carried = f.extract r.carriedAt f.size ∧
      w₀.height = r.head.height := by
  obtain ⟨hdg, _, _, hb, hh⟩ := read_ok hd hr
  have hc := Receive.carry_carried hw
  refine ⟨hdg, by rw [hc, hb], ?_⟩
  rw [hh, ← hc]; rfl

theorem exportCheck_reads [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {dc : Stream D} {w : World D}
    {f f' : ByteArray} (h : exportCheck E dc w f = .ok f') :
    f' = f ∧ ∃ r, read E dc (digestOf f) f = .ok r ∧
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

/-- `importWorld` accepts exactly what `read` then `world` accept. -/
theorem importWorld_ok {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray} {want : Digest}
    {f : ByteArray} {w : World D} {r : Read D}
    (h : importWorld X dc name nonce want f = .ok (w, r)) :
    read X.env dc want f = .ok r ∧ world X name nonce r = .ok w := by
  unfold importWorld at h
  split at h
  · cases h
  · cases h
  · rename_i r' hr
    split at h
    · rename_i w' hw
      cases h
      exact ⟨hr, hw⟩
    all_goals cases h

/-- **What export writes, import reads back**: the exported World's carried bytes and its head
(origin, the lineage `import` commits in the new origin; height and chain, the anchor), under the
digest export prints. -/
theorem exportFile_reads [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {dc : Stream D} {w : World D}
    {f : ByteArray} (h : exportFile E dc w = .ok f) :
    ∃ r, read E dc (digestOf f) f = .ok r ∧ (carried E dc).bytes r.carried = (carried E dc).bytes w.carried ∧
      r.head = ⟨w.origin, w.height, w.chain⟩ := by
  obtain ⟨rfl, hr⟩ := exportCheck_reads h
  exact hr

/-- **Export refuses no fitting World** (completeness). NOT discharged at Deployed: an opened World's
`Carried.CodecFits` needs `World.CodecFits` of a decoded base folded by admission (no theorem yet)
and `journal.size < journalMax` (KERNEL's bound, strict, where `CodecFits` allows `≤`). Soundness
does not rest on it: export re-reads its file (`exportCheck`) and refuses rather than write a bad
one. -/
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
  have hread : read E dc (digestOf (file E dc w)) (file E dc w) =
      .ok ⟨⟨w.origin, w.height, w.chain⟩, w.carried, stampBytes + H.size⟩ := by
    unfold read
    rw [if_neg (by simp), if_neg (by simp [hst']), hget]
    dsimp only
    rw [htail, hdec]
    dsimp only
    rw [if_neg (by simp [World.carried])]
  unfold exportFile exportCheck
  rw [hread]
  dsimp only
  rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]

end Nanodregg.Host.Carry
