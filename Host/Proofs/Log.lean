/-
# Host.Proofs.Log — what `Host.Log.recover` guarantees

* `recover_encodeAll` — a segment written by `encodeAll` reads back exactly, `clean`.
* `recover_torn` — cut the next frame anywhere (a crash before its fsync): the frames before it
  read back exactly, and the tail is `torn` with the cut length (`clean` if the cut is empty).
* `encodeAll_recover` — for ANY bytes, the records `recover` returns re-encode to exactly the
  bytes before `validLen`, and `lastTag` is their chain's tag: recovery never invents a record.
-/
import Host.Log

namespace Nanodregg.Host.Log

open ByteArray

theorem size_le32 (n : Nat) : (le32 n).size = 4 := rfl

theorem ofLe32_le32 {n : Nat} (h : n < 2 ^ 32) : ofLe32 (le32 n) = n := by
  have e0 : (le32 n)[0]! = UInt8.ofNat n := rfl
  have e1 : (le32 n)[1]! = UInt8.ofNat (n / 256) := rfl
  have e2 : (le32 n)[2]! = UInt8.ofNat (n / 65536) := rfl
  have e3 : (le32 n)[3]! = UInt8.ofNat (n / 16777216) := rfl
  simp only [ofLe32, e0, e1, e2, e3, UInt8.toNat_ofNat', Nat.reducePow]
  omega

theorem size_frame (s : Sealer) (prev r : ByteArray) :
    (frame s prev r).size = 4 + r.size + tagBytes := by
  simp [frame, size_append, size_le32, s.tag_size]

/-- Reading inside the right half of an append. -/
theorem extract_right {log a b : ByteArray} (h : log = a ++ b) (i j : Nat) :
    log.extract (a.size + i) (a.size + j) = b.extract i j := by
  subst h; exact extract_append_size_add

/-- The three fields of `L ‖ R ‖ T ‖ C`, by their sizes. -/
theorem fields {L R T C : ByteArray} (hl : L.size = 4) :
    (L ++ R ++ T ++ C).extract 0 4 = L ∧
    (L ++ R ++ T ++ C).extract 4 (4 + R.size) = R ∧
    (L ++ R ++ T ++ C).extract (4 + R.size) (4 + R.size + T.size) = T := by
  refine ⟨?_, ?_, ?_⟩
  · rw [append_assoc, append_assoc]
    exact extract_append_eq_left hl.symm
  · have h := extract_append_size_add' (a := L) (b := R ++ (T ++ C)) (i := 0) (j := R.size) hl.symm
    simp only [Nat.add_zero] at h
    rw [append_assoc, append_assoc, h]
    exact extract_append_eq_left rfl
  · have k : 4 + R.size = (L ++ R).size := by simp [size_append, hl]
    have h := extract_append_size_add' (a := L ++ R) (b := T ++ C) (i := 0) (j := T.size) k
    simp only [Nat.add_zero] at h
    rw [append_assoc (a := L ++ R), h]
    exact extract_append_eq_left rfl

theorem frame_fields (s : Sealer) (prev r c : ByteArray) :
    (frame s prev r ++ c).extract 0 4 = le32 r.size ∧
    (frame s prev r ++ c).extract 4 (4 + r.size) = r ∧
    (frame s prev r ++ c).extract (4 + r.size) (4 + r.size + tagBytes) = s.tag (prev ++ r) := by
  have := fields (R := r) (T := s.tag (prev ++ r)) (C := c) (size_le32 r.size)
  rw [s.tag_size] at this
  exact this

/-- `step` reads a well-formed frame at its offset. -/
theorem step_frame (s : Sealer) {recordMax : Nat} (a : ByteArray) (prev r c : ByteArray)
    (hr : r.size ≤ recordMax) (hr32 : r.size < 2 ^ 32) :
    step s recordMax (a ++ (frame s prev r ++ c)) a.size prev =
      .next r (a.size + (frame s prev r).size) (s.tag (prev ++ r)) := by
  obtain ⟨f0, f1, f2⟩ := frame_fields s prev r c
  have hsz : (a ++ (frame s prev r ++ c)).size = a.size + (4 + r.size + tagBytes) + c.size := by
    simp [size_append, size_frame]; omega
  have hread : readLe32 (a ++ (frame s prev r ++ c)) a.size = some r.size := by
    unfold readLe32
    rw [if_pos (by rw [hsz]; omega)]
    rw [show a.size + 4 = a.size + 4 from rfl,
      show a.size = a.size + 0 from rfl]
    rw [extract_right rfl 0 4, f0, ofLe32_le32 hr32]
  have e1 := extract_right (rfl : a ++ (frame s prev r ++ c) = _) 4 (4 + r.size)
  have e2 := extract_right (rfl : a ++ (frame s prev r ++ c) = _) (4 + r.size) (4 + r.size + tagBytes)
  rw [f1] at e1; rw [f2] at e2
  unfold step
  rw [if_neg (by rw [hsz]; simp [tagBytes]; omega), hread]
  simp only
  rw [if_neg (by omega), if_neg (by rw [hsz]; omega)]
  rw [show a.size + 4 + r.size = a.size + (4 + r.size) by omega,
    show a.size + (4 + r.size) + tagBytes = a.size + (4 + r.size + tagBytes) by omega, e1, e2,
    if_pos rfl, size_frame]

/-- Size of a segment. -/
theorem size_encodeAll_ge (s : Sealer) (prev : ByteArray) (rs : List ByteArray) :
    rs.length * (4 + tagBytes) ≤ (encodeAll s prev rs).size := by
  induction rs generalizing prev with
  | nil => simp [encodeAll]
  | cons r rs ih =>
    simp only [encodeAll, size_append, size_frame, List.length_cons]
    have := ih (s.tag (prev ++ r))
    rw [Nat.succ_mul]; omega

/-- `go` walks a well-formed run of frames, consuming one fuel per frame. -/
theorem go_encodeAll (s : Sealer) {recordMax : Nat} (rs : List ByteArray)
    (hrs : ∀ r ∈ rs, r.size ≤ recordMax ∧ r.size < 2 ^ 32) :
    ∀ (a c prev : ByteArray) (acc : List ByteArray) (fuel : Nat), rs.length ≤ fuel →
      go s recordMax (a ++ (encodeAll s prev rs ++ c)) fuel a.size prev acc =
        go s recordMax (a ++ (encodeAll s prev rs ++ c)) (fuel - rs.length)
          (a.size + (encodeAll s prev rs).size) (lastTag s prev rs) (rs.reverse ++ acc) := by
  induction rs with
  | nil => intro a c prev acc fuel _; simp [encodeAll, lastTag]
  | cons r rs ih =>
    intro a c prev acc fuel hf
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hr := hrs r (by simp)
    have hrs' : ∀ x ∈ rs, x.size ≤ recordMax ∧ x.size < 2 ^ 32 := fun x hx => hrs x (by simp [hx])
    have hlog : a ++ (encodeAll s prev (r :: rs) ++ c) =
        a ++ (frame s prev r ++ (encodeAll s (s.tag (prev ++ r)) rs ++ c)) := by
      simp [encodeAll, append_assoc]
    rw [hlog]
    simp only [go]
    rw [step_frame s a prev r _ hr.1 hr.2]
    simp only
    have hlog2 : a ++ (frame s prev r ++ (encodeAll s (s.tag (prev ++ r)) rs ++ c)) =
        (a ++ frame s prev r) ++ (encodeAll s (s.tag (prev ++ r)) rs ++ c) := by
      simp [append_assoc]
    rw [hlog2, show a.size + (frame s prev r).size = (a ++ frame s prev r).size by simp [size_append]]
    rw [ih hrs' (a ++ frame s prev r) c (s.tag (prev ++ r)) (r :: acc) fuel (by simp at hf; omega)]
    simp [encodeAll, lastTag, size_append, Nat.add_assoc]

theorem recover_encodeAll (s : Sealer) {recordMax : Nat} (initial : ByteArray) (rs : List ByteArray)
    (hrs : ∀ r ∈ rs, r.size ≤ recordMax ∧ r.size < 2 ^ 32) :
    recover s recordMax initial (encodeAll s initial rs) =
      ⟨rs, (encodeAll s initial rs).size, lastTag s initial rs, .clean⟩ := by
  have hge := size_encodeAll_ge s initial rs
  have h := go_encodeAll s rs hrs ByteArray.empty ByteArray.empty initial [] ((encodeAll s initial rs).size + 1)
    (by simp [tagBytes] at hge ⊢; omega)
  simp only [empty_append, append_empty, size_empty, Nat.zero_add, List.append_nil] at h
  unfold recover
  rw [h]
  obtain ⟨k, hk⟩ : ∃ k, (encodeAll s initial rs).size + 1 - rs.length = k + 1 :=
    ⟨(encodeAll s initial rs).size - rs.length, by simp [tagBytes] at hge; omega⟩
  rw [hk]
  simp [go, step, List.reverse_reverse]

/-- The step after a clean run, when the next frame was cut after `p`. -/
theorem step_cut (s : Sealer) {recordMax : Nat} (E prev r p q : ByteArray)
    (hr : r.size ≤ recordMax ∧ r.size < 2 ^ 32)
    (hcut : p ++ q = frame s prev r) (hq : 0 < q.size) :
    step s recordMax (E ++ p) E.size prev =
      if p.size = 0 then .stop .clean else .stop (.torn p.size) := by
  have hpq : p.size + q.size = 4 + r.size + tagBytes := by
    rw [← size_frame s prev r, ← hcut, size_append]
  have hsize : (E ++ p).size = E.size + p.size := size_append
  have hbad : badTail recordMax (E ++ p) E.size = .torn p.size := by
    unfold badTail frameMax; rw [if_pos (by rw [hsize]; omega), hsize, Nat.add_sub_cancel_left]
  by_cases hp0 : p.size = 0
  · rw [if_pos hp0]; unfold step; rw [if_pos (by rw [hsize]; omega)]
  · rw [if_neg hp0]
    unfold step
    rw [if_neg (by rw [hsize]; omega)]
    by_cases h4 : p.size < 4
    · have : readLe32 (E ++ p) E.size = none := by
        unfold readLe32; rw [if_neg (by rw [hsize]; omega)]
      rw [this, hbad]
    · have hhead : (E ++ p).extract E.size (E.size + 4) = le32 r.size := by
        have := extract_right (rfl : E ++ p = _) 0 4
        simp only [Nat.add_zero] at this
        rw [this]
        have hp4 : p.extract 0 4 = (p ++ q).extract 0 4 := by
          rw [extract_append, show 4 - p.size = 0 by omega, Nat.zero_sub, extract_same, append_empty]
        rw [hp4, hcut]
        have := (frame_fields s prev r ByteArray.empty).1
        rwa [append_empty] at this
      have : readLe32 (E ++ p) E.size = some r.size := by
        unfold readLe32; rw [if_pos (by rw [hsize]; omega), hhead, ofLe32_le32 hr.2]
      rw [this]
      simp only
      have h1 := hr.1
      rw [if_neg (by omega), if_pos (by rw [hsize]; omega), hbad]

/-- A cut inside the frame after a clean run reads as `torn` with the cut length. -/
theorem recover_torn (s : Sealer) {recordMax : Nat} (initial : ByteArray) (rs : List ByteArray)
    (hrs : ∀ r ∈ rs, r.size ≤ recordMax ∧ r.size < 2 ^ 32)
    (r p q : ByteArray) (hr : r.size ≤ recordMax ∧ r.size < 2 ^ 32)
    (hcut : p ++ q = frame s (lastTag s initial rs) r) (hq : 0 < q.size) :
    recover s recordMax initial (encodeAll s initial rs ++ p) =
      ⟨rs, (encodeAll s initial rs).size, lastTag s initial rs,
        if p.size = 0 then .clean else .torn p.size⟩ := by
  have hge := size_encodeAll_ge s initial rs
  have h := go_encodeAll s rs hrs ByteArray.empty p initial []
    ((encodeAll s initial rs ++ p).size + 1) (by simp [size_append, tagBytes] at hge ⊢; omega)
  simp only [empty_append, size_empty, Nat.zero_add, List.append_nil] at h
  unfold recover
  rw [h]
  obtain ⟨k, hk⟩ : ∃ k, (encodeAll s initial rs ++ p).size + 1 - rs.length = k + 1 :=
    ⟨(encodeAll s initial rs ++ p).size - rs.length, by simp [size_append, tagBytes] at hge ⊢; omega⟩
  rw [hk]
  simp only [go, List.reverse_reverse]
  rw [step_cut s _ _ r p q hr hcut hq]
  by_cases hp0 : p.size = 0 <;> simp [hp0]

/-- Every four bytes are the encoding of their value. -/
theorem le32_ofLe32 {b : ByteArray} (h : b.size = 4) : le32 (ofLe32 b) = b := by
  obtain ⟨⟨l⟩⟩ := b
  match l, h with
  | [a0, a1, a2, a3], _ =>
    have e0 : (ByteArray.mk #[a0, a1, a2, a3])[0]! = a0 := rfl
    have e1 : (ByteArray.mk #[a0, a1, a2, a3])[1]! = a1 := rfl
    have e2 : (ByteArray.mk #[a0, a1, a2, a3])[2]! = a2 := rfl
    have e3 : (ByteArray.mk #[a0, a1, a2, a3])[3]! = a3 := rfl
    simp only [le32, ofLe32, e0, e1, e2, e3]
    have b0 := a0.toNat_lt; have b1 := a1.toNat_lt; have b2 := a2.toNat_lt; have b3 := a3.toNat_lt
    simp only [ByteArray.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (apply UInt8.toNat_inj.mp; simp only [UInt8.toNat_ofNat', Nat.reducePow] at *; omega)

theorem encodeAll_snoc (s : Sealer) (prev : ByteArray) (xs : List ByteArray) (r : ByteArray) :
    encodeAll s prev (xs ++ [r]) = encodeAll s prev xs ++ frame s (lastTag s prev xs) r := by
  induction xs generalizing prev with
  | nil => simp [encodeAll, lastTag]
  | cons x xs ih => simp [encodeAll, lastTag, ih, append_assoc]

theorem lastTag_snoc (s : Sealer) (prev : ByteArray) (xs : List ByteArray) (r : ByteArray) :
    lastTag s prev (xs ++ [r]) = s.tag (lastTag s prev xs ++ r) := by
  induction xs generalizing prev with
  | nil => simp [lastTag]
  | cons x xs ih => simp [lastTag, ih]

/-- What a `next` step read is literally a frame on disk. -/
theorem step_next {s : Sealer} {recordMax : Nat} {log : ByteArray} {off : Nat} {prev r : ByteArray}
    {o : Nat} {t : ByteArray} (h : step s recordMax log off prev = .next r o t) :
    off ≤ o ∧ o ≤ log.size ∧ log.extract off o = frame s prev r ∧ t = s.tag (prev ++ r) := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i len hread
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hlen hfit
          dsimp only at h
          split at h
          · rename_i htag
            cases h
            unfold readLe32 at hread
            split at hread
            · rename_i h4
              cases hread
              refine ⟨by omega, by omega, ?_, htag.symm⟩
              have hr : (log.extract (off + 4) (off + 4 + ofLe32 (log.extract off (off + 4)))).size =
                  ofLe32 (log.extract off (off + 4)) := by simp; omega
              unfold frame
              rw [hr, le32_ofLe32 (by simp; omega), htag,
                ← extract_eq_extract_append_extract (off + 4) (by omega) (by omega),
                ← extract_eq_extract_append_extract (off + 4 + ofLe32 (log.extract off (off + 4)))
                  (by omega) (by omega)]
            · cases hread
          · cases h

/-- For any bytes: the records recovered re-encode to exactly the bytes before `validLen`. -/
theorem go_sound (s : Sealer) (recordMax : Nat) (initial log : ByteArray) :
    ∀ (fuel off : Nat) (prev : ByteArray) (acc : List ByteArray), off ≤ log.size →
      log.extract 0 off = encodeAll s initial acc.reverse → prev = lastTag s initial acc.reverse →
      log.extract 0 (go s recordMax log fuel off prev acc).validLen =
          encodeAll s initial (go s recordMax log fuel off prev acc).records ∧
        (go s recordMax log fuel off prev acc).lastTag =
          lastTag s initial (go s recordMax log fuel off prev acc).records := by
  intro fuel
  induction fuel with
  | zero => intro off prev acc _ he ht; exact ⟨he, ht⟩
  | succ fuel ih =>
    intro off prev acc hoff he ht
    simp only [go]
    split
    · exact ⟨he, ht⟩
    · rename_i r o t hstep
      obtain ⟨h1, h2, h3, h4⟩ := step_next hstep
      apply ih o t (r :: acc) h2
      · rw [List.reverse_cons, encodeAll_snoc, ← ht, ← he, ← h3,
          ← extract_eq_extract_append_extract off (Nat.zero_le _) h1]
      · rw [List.reverse_cons, lastTag_snoc, ← ht, h4]

theorem encodeAll_recover (s : Sealer) (recordMax : Nat) (initial log : ByteArray) :
    log.extract 0 (recover s recordMax initial log).validLen =
        encodeAll s initial (recover s recordMax initial log).records ∧
      (recover s recordMax initial log).lastTag =
        lastTag s initial (recover s recordMax initial log).records :=
  go_sound s recordMax initial log _ 0 initial [] (Nat.zero_le _)
    (by simp [encodeAll]) (by simp [lastTag])

end Nanodregg.Host.Log
