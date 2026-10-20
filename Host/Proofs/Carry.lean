/-
# Host.Proofs.Carry — what `host import` accepts, and that what `host export` writes imports (HOST-28)

* `read_ok` — a file `Carry.read` accepts carries this binary's stamp at its head, and its carried
  bytes are exactly the bytes after its head (CODEC's canonical decode: no other spelling reads back);
* `importWorld_ok` — an import accepts exactly what its pin (`Pin.Holds`: the file's digest, or the
  made World's origin), `read` and `world` accept;
* `importWorld_digest` / `read_stamp` / `importWorld_wrongWorld` — the teeth: any other digest is
  refused `digest` before a byte is decoded, any other stamp `shapeMismatch`, and a carry making a
  World of another origin than the pinned one `carryMismatch wrongWorld`, before anything is written;
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

theorem read_stamp (E : Env D) (dc : Stream D) {f : ByteArray} (h : f.extract 0 stampBytes ≠ (stamp E dc).bytes) :
    read E dc f = .error (.stamp (f.extract 0 stampBytes)) := by
  unfold read; rw [if_pos h]

/-- What an import's pin demands of its file and the World it makes. -/
def Pin.Holds : Pin D → ByteArray → World D → Prop
  | .digest want, f, _ => digestOf f = want
  | .origin o, _, w => w.origin = o

/-- **Tooth: a digest pin refuses any other file** `carryMismatch digest`, before a byte is read. -/
theorem importWorld_digest (X : Receive.Ctx D) (dc : Stream D) (name nonce : ByteArray) {want : Digest}
    {f : ByteArray} (h : digestOf f ≠ want) :
    importWorld X dc name nonce (.digest want) f = .error (.carryMismatch, "carryMismatch digest") := by
  unfold importWorld; simp only [if_pos h]; rfl

/-- **Tooth: an origin pin refuses a World of another origin** `carryMismatch wrongWorld`: the file
reads and KERNEL's carry makes `w`, and still nothing is imported (`import --origin`, card 7a). -/
theorem importWorld_wrongWorld {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray} {o : D}
    {f : ByteArray} {r : Read D} {w : World D} (hr : read X.env dc f = .ok r)
    (hw : world X name nonce r = .ok w) (ho : w.origin ≠ o) :
    importWorld X dc name nonce (.origin o) f = .error (.carryMismatch, "carryMismatch wrongWorld") := by
  unfold importWorld carryFile
  rw [hr]
  simp only [hw, ho, decide_false, Bool.false_eq_true, if_false]
  rfl

/-- **An import holds exactly the file's carried bytes**, at the file's anchor height. -/
theorem world_carried [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {X : Receive.Ctx D} {name nonce : ByteArray} {f : ByteArray}
    {r : Read D} {w₀ : World D}
    (hr : read E dc f = .ok r) (hw : world X name nonce r = .ok w₀) :
    (carried E dc).bytes w₀.carried = f.extract r.carriedAt f.size ∧
      w₀.height = r.head.height := by
  obtain ⟨_, _, hb, hh⟩ := read_ok hd hr
  have hc := Receive.carry_carried hw
  refine ⟨by rw [hc, hb], ?_⟩
  rw [hh, ← hc]; rfl

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
    {f : ByteArray} {accept : World D → Bool} {w : World D} {r : Read D}
    (h : carryFile X dc name nonce f accept = .ok (w, r)) :
    read X.env dc f = .ok r ∧ world X name nonce r = .ok w ∧ accept w = true := by
  unfold carryFile at h
  split at h
  · cases h
  · cases h
  · rename_i r' hr
    split at h
    · rename_i w' hw
      split at h
      · rename_i ha
        cases h
        exact ⟨hr, hw, ha⟩
      · cases h
    all_goals cases h

/-- `importWorld` accepts only what its pin, `read` and `world` accept. -/
theorem importWorld_ok {X : Receive.Ctx D} {dc : Stream D} {name nonce : ByteArray} {pin : Pin D}
    {f : ByteArray} {w : World D} {r : Read D}
    (h : importWorld X dc name nonce pin f = .ok (w, r)) :
    read X.env dc f = .ok r ∧ world X name nonce r = .ok w ∧ pin.Holds f w := by
  unfold importWorld at h
  cases pin with
  | digest want =>
    simp only at h
    split at h
    · cases h
    · rename_i hd
      obtain ⟨hr, hw, -⟩ := carryFile_ok h
      exact ⟨hr, hw, by simpa [Pin.Holds] using hd⟩
  | origin o =>
    obtain ⟨hr, hw, ha⟩ := carryFile_ok h
    exact ⟨hr, hw, by simpa [Pin.Holds] using ha⟩

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
