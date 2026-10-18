/-
# Host.Proofs.Backup — what a live backup in `Store.backupOrder` opens to (HOST-32)

A backup of a LIVE Store copies `key`, then `base.world`, then `index.log`, then `seg.log`
(`Host.Store.backupOrder`). The base is replaced atomically, so the copy holds one base the writer
installed; `index.log` and `seg.log` are append-only, so each copy is the file as it stood when the
base was copied, plus whatever the writer appended since (`I ++ x`, `S ++ y`).

* `recover_append` — appending bytes after a segment never loses a frame it held: the records
  recovered from `log` are a prefix of those recovered from `log ++ y`;
* `openLog_append` — the open of `tail ++ y` from the same World folds every record the open of
  `tail` folded and then more, or refuses by name (`corrupt`, or `record j` at a record past them);
* `openWith_backup` — **the backup theorem.** If the Store as it stood when its base was copied
  opens (the writer's invariant: every instant of a live Store opens, which host-sim's crash plants
  test), then the backup opens to the same base, at least as many records, a World that is the
  live one advanced by the extra records, and an index that extends the live one; or it refuses by
  name — `tailTooLong` (the writer sealed and kept appending while the copy ran), `corrupt`, or
  `record j` past the live records. It never opens SILENTLY SHORT, and it never refuses
  `indexShort`, `indexCorrupt`, `foreignSegment` or `foreignOrigin`: the base's prefixes are in the
  copies because they were in the files when the base was copied.

* `openWith_cut` — the files cut to an open's valid end and to the entries its base counts open
  to the same Store, with no torn tail and no orphans: every read the open makes lies in the cut;
* `openWith_backup_restart` — **the backup theorem across restarts.** A writer that RESTARTS
  between two copies truncates a torn tail and orphan entries (`openWriter`), so its later copies
  are `S.extract 0 o.pos.offset ++ y` and `I.extract 0 (count * entryBytes) ++ x`, not `S ++ y` and
  `I ++ x`. They open as `openWith_backup` says (`openWith_cut`, then `openWith_backup` on the cut
  files), which this generalizes.

Premises, the writer's invariants, not proved; tested by host-sim's crash plants and
host-file-sim's `restartPlants`: the Store as it stood when the backup copied base.world opens (to
`o`), and the live open read only synced bytes, which the writer's own opens do (a follower can
read page-cache bytes never synced, and a power loss then shrinks seg.log below `o.pos.offset`
with no restart involved); seg.log[0, o.pos.offset) and index.log[0, count · entryBytes) were
durable when the backup copied base.world, and are never rewritten; a restart (`openWriter`) cuts
only past its own open's valid end and count, which are at or past these (a later base sits at or
past the live valid end and counts at least the live entries).
-/
import Host.Proofs.Base
import Host.Proofs.Open

namespace Nanodregg.Host

open Nanodregg.Host.Log ByteArray

/-! ## Bytes -/

theorem extract_append_le {a b : ByteArray} {i j : Nat} (hj : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  rw [extract_append]
  have : b.extract (i - a.size) (j - a.size) = ByteArray.empty := by
    rw [extract_eq_empty_iff]; omega
  rw [this, ByteArray.append_empty]

theorem occursAt_append_right {b c w : ByteArray} {i : Nat} (h : Codec.Stream.OccursAt b i w) :
    Codec.Stream.OccursAt (b ++ c) i w :=
  ⟨by rw [size_append]; have := h.1; omega, by rw [extract_append_le h.1]; exact h.2⟩

/-! ## Frames survive an append -/

theorem lenAt_append {log y : ByteArray} {off n : Nat} (h : lenAt log off = some n) :
    lenAt (log ++ y) off = some n := by
  unfold lenAt at h ⊢
  split at h
  · rename_i v j hget
    cases h
    obtain ⟨_, ho⟩ := Codec.Stream.u32_lawful.occurs_of_get hget
    rw [Codec.Stream.u32_lawful.get_of_occurs _ _ _ (occursAt_append_right ho)]
  · cases h

theorem frameAt_append {s : Sealer} {m : Nat} {log y : ByteArray} {off : Nat} {prev : ByteArray}
    {rd : Read} (h : frameAt s m log off prev = some rd) : frameAt s m (log ++ y) off prev = some rd := by
  unfold frameAt at h ⊢
  cases hread : lenAt log off with
  | none => rw [hread] at h; cases h
  | some len =>
    rw [hread] at h
    rw [lenAt_append hread]
    dsimp only at h ⊢
    by_cases h1 : m < len
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h ⊢
    by_cases h2 : log.size < off + 4 + len + tagBytes
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    rw [if_neg (by rw [size_append]; omega), extract_append_le (by omega), extract_append_le (by omega)]
    exact h

theorem step_append {s : Sealer} {m : Nat} {log y : ByteArray} {off : Nat} {prev r : ByteArray}
    {o : Nat} {t : ByteArray} (h : step s m log off prev = .next r o t) :
    step s m (log ++ y) off prev = .next r o t := by
  unfold step at h ⊢
  by_cases h0 : log.size ≤ off
  · rw [if_pos h0] at h; cases h
  rw [if_neg h0] at h
  rw [if_neg (by rw [size_append]; omega)]
  cases hf : frameAt s m log off prev with
  | none => rw [hf] at h; cases h
  | some rd => rw [hf] at h; rw [frameAt_append hf]; exact h

theorem go_records_prefix (s : Sealer) (m : Nat) (log : ByteArray) :
    ∀ (fuel off : Nat) (prev : ByteArray) (acc : List ByteArray),
      acc.reverse <+: (go s m log fuel off prev acc).records := by
  intro fuel
  induction fuel with
  | zero => intro off prev acc; exact List.prefix_refl _
  | succ fuel ih =>
    intro off prev acc
    simp only [go]
    split
    · exact List.prefix_refl _
    · rename_i r o t _
      exact (List.prefix_append acc.reverse [r]).trans (by simpa using ih o t (r :: acc))

theorem go_append (s : Sealer) (m : Nat) (log y : ByteArray) :
    ∀ (f' f off : Nat) (prev : ByteArray) (acc : List ByteArray), f' ≤ f →
      (go s m log f' off prev acc).records <+: (go s m (log ++ y) f off prev acc).records := by
  intro f'
  induction f' with
  | zero => intro f off prev acc _; exact go_records_prefix s m (log ++ y) f off prev acc
  | succ f' ih =>
    intro f off prev acc hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    cases hs : step s m log off prev with
    | stop tail =>
      rw [show go s m log (f' + 1) off prev acc = ⟨acc.reverse, off, prev, tail⟩ by simp only [go, hs]]
      exact go_records_prefix s m (log ++ y) (g + 1) off prev acc
    | next r o t =>
      rw [show go s m log (f' + 1) off prev acc = go s m log f' o t (r :: acc) by simp only [go, hs],
        show go s m (log ++ y) (g + 1) off prev acc = go s m (log ++ y) g o t (r :: acc) by
          simp only [go, step_append hs]]
      exact ih g o t (r :: acc) (by omega)

theorem encodeAll_append (s : Sealer) (prev : ByteArray) (xs ys : List ByteArray) :
    encodeAll s prev (xs ++ ys) = encodeAll s prev xs ++ encodeAll s (lastTag s prev xs) ys := by
  induction xs generalizing prev with
  | nil => simp [encodeAll, lastTag]
  | cons x xs ih => simp [encodeAll, lastTag, ih, append_assoc]

/-- **Appending never loses a frame.** -/
theorem recover_append (s : Sealer) (m : Nat) (initial log y : ByteArray) :
    (recover s m initial log).records <+: (recover s m initial (log ++ y)).records :=
  go_append s m log y _ _ 0 initial [] (by rw [size_append]; omega)

/-! ## The fold of a longer tail -/

variable {W F : Type}

theorem foldRecords_append (step : W → ByteArray → Except F W) :
    ∀ (rs more : List ByteArray) (w w₁ : W) (i : Nat), foldRecords step w i rs = .ok w₁ →
      foldRecords step w i (rs ++ more) = foldRecords step w₁ (i + rs.length) more
  | [], more, w, w₁, i, h => by simp only [foldRecords, Except.ok.injEq] at h; subst h; simp
  | r :: rs, more, w, w₁, i, h => by
    simp only [foldRecords] at h
    simp only [List.cons_append, foldRecords]
    split at h
    · rename_i w' hw
      rw [foldRecords_append step rs more w' w₁ (i + 1) h]
      simp [Nat.add_assoc, Nat.add_comm 1]
    · cases h

theorem foldRecords_error (step : W → ByteArray → Except F W) :
    ∀ (rs : List ByteArray) (w : W) (i : Nat) {e : OpenFault F}, foldRecords step w i rs = .error e →
      ∃ j f, e = .record j f ∧ i ≤ j ∧ j < i + rs.length
  | [], w, i, e, h => by simp [foldRecords] at h
  | r :: rs, w, i, e, h => by
    simp only [foldRecords] at h
    split at h
    · obtain ⟨j, f, rfl, h1, h2⟩ := foldRecords_error step rs _ (i + 1) h
      exact ⟨j, f, rfl, by omega, by simp; omega⟩
    · rename_i f _
      cases h
      exact ⟨i, f, rfl, Nat.le_refl _, by simp⟩

theorem badTail_corrupt {s : Sealer} {m : Nat} {log : ByteArray} {off o : Nat}
    (h : badTail s m log off = .corrupt o) : o = off := by
  unfold badTail at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/-- A recovery that ends `corrupt` ends it where its valid bytes end. -/
theorem go_corrupt (s : Sealer) (m : Nat) (log : ByteArray) :
    ∀ (fuel off : Nat) (prev : ByteArray) (acc : List ByteArray) {o : Nat},
      (go s m log fuel off prev acc).tail = .corrupt o → o = (go s m log fuel off prev acc).validLen := by
  intro fuel
  induction fuel with
  | zero => intro off prev acc o h; simp only [go] at h ⊢; cases h; rfl
  | succ fuel ih =>
    intro off prev acc o h
    simp only [go] at h ⊢
    split at h
    · rename_i tail hst
      try simp only at h ⊢
      unfold step at hst
      split at hst
      · cases hst; cases h
      · split at hst
        · cases hst
        · cases hst; exact badTail_corrupt h
    · rename_i r o' t _
      try simp only at h ⊢
      exact ih o' t (r :: acc) h

/-- **The open of a longer tail.** From the same World, `tail ++ y` folds every record `tail`
folded, then `more`, or refuses `corrupt` or `record j` past them; never fewer records. -/
theorem openLog_append (s : Sealer) (m : Nat) (step : W → ByteArray → Except F W) (w₀ : W)
    (initial tail y : ByteArray) {o : Opened W} (h : openLog s m step w₀ initial tail = .ok o) :
    (∃ o' more, openLog s m step w₀ initial (tail ++ y) = .ok o' ∧
      foldRecords step o.world o.records more = .ok o'.world ∧ o'.records = o.records + more.length ∧
      o.validLen ≤ o'.validLen) ∨
    (∃ off, openLog s m step w₀ initial (tail ++ y) = .error (.corrupt off) ∧ o.validLen ≤ off) ∨
    (∃ j f, openLog s m step w₀ initial (tail ++ y) = .error (.record j f) ∧ o.records ≤ j) := by
  obtain ⟨more, hm⟩ := recover_append s m initial tail y
  have hs := encodeAll_recover s m initial tail
  have hs' := encodeAll_recover s m initial (tail ++ y)
  have hv := recover_validLen_le s m initial tail
  have hv' := recover_validLen_le s m initial (tail ++ y)
  have hc : ∀ {o}, (recover s m initial (tail ++ y)).tail = .corrupt o →
      o = (recover s m initial (tail ++ y)).validLen := fun h => go_corrupt s m (tail ++ y) _ 0 initial [] h
  unfold openLog at h ⊢
  generalize hrv : recover s m initial tail = rv at h hm hs hv
  generalize hrv' : recover s m initial (tail ++ y) = rv' at hm hs' hv' hc ⊢
  have hvl : rv.validLen ≤ rv'.validLen := by
    have h1 := congrArg ByteArray.size hs.1
    have h2 := congrArg ByteArray.size hs'.1
    rw [← hm, encodeAll_append, size_append] at h2
    simp only [size_extract] at h1 h2
    omega
  simp only at h ⊢
  split at h
  · cases h
  · split at h
    · rename_i w hw
      cases h
      split
      · rename_i off hoff
        exact Or.inr (Or.inl ⟨off, rfl, by rw [hc hoff]; exact hvl⟩)
      · rw [← hm, foldRecords_append step rv.records more w₀ w 0 hw]
        cases hf : foldRecords step w (0 + rv.records.length) more with
        | ok w' =>
          exact Or.inl ⟨_, more, rfl, by simpa using hf, by simp, hvl⟩
        | error e =>
          obtain ⟨j, f, rfl, hj, _⟩ := foldRecords_error step more w _ hf
          exact Or.inr (Or.inr ⟨j, f, rfl, by simpa using hj⟩)
    · cases h

/-! ## Where an indexed fold ends -/

theorem size_encodeAll_sum (s : Sealer) :
    ∀ (p : ByteArray) (rs : List ByteArray), (encodeAll s p rs).size = (rs.map frameSize).sum
  | _, [] => rfl
  | _, r :: rs => by
    simp only [encodeAll, size_append, size_frame, size_encodeAll_sum s _ rs, List.map_cons,
      List.sum_cons, frameSize]

theorem indexed_foldlM_off (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) :
    ∀ (rs : List ByteArray) (w : W) (idx : Array Entry) (off : Nat) {st : W × Array Entry × Nat},
      rs.foldlM (indexed mark step) (w, idx, off) = .ok st → st.2.2 = off + (rs.map frameSize).sum
  | [], w, idx, off, st, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | r :: rs, w, idx, off, st, h => by
    simp only [List.foldlM] at h
    cases hs : step w r with
    | error e => simp [indexed, hs, bind, Except.bind] at h
    | ok w' =>
      simp only [indexed, hs, bind, Except.bind, pure, Except.pure] at h
      have := indexed_foldlM_off mark step rs _ _ _ h
      simp only [List.map_cons, List.sum_cons]
      omega

theorem indexed_foldlM_fst (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) :
    ∀ (rs : List ByteArray) (w : W) (idx : Array Entry) (off : Nat) {st : W × Array Entry × Nat},
      rs.foldlM (indexed mark step) (w, idx, off) = .ok st → rs.foldlM step w = .ok st.1
  | [], w, idx, off, st, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  | r :: rs, w, idx, off, st, h => by
    simp only [List.foldlM] at h ⊢
    cases hs : step w r with
    | error e => simp [indexed, hs, bind, Except.bind] at h
    | ok w' =>
      simp only [indexed, hs, bind, Except.bind, pure, Except.pure] at h
      simp only [bind, Except.bind]
      exact indexed_foldlM_fst mark step rs _ _ _ h

theorem indexed_foldlM_size (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) :
    ∀ (rs : List ByteArray) (w : W) (idx : Array Entry) (off : Nat) {st : W × Array Entry × Nat},
      rs.foldlM (indexed mark step) (w, idx, off) = .ok st → st.2.1.size = idx.size + rs.length
  | [], w, idx, off, st, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | r :: rs, w, idx, off, st, h => by
    simp only [List.foldlM] at h
    cases hs : step w r with
    | error e => simp [indexed, hs, bind, Except.bind] at h
    | ok w' =>
      simp only [indexed, hs, bind, Except.bind, pure, Except.pure] at h
      have := indexed_foldlM_size mark step rs _ _ _ h
      simp only [Array.size_push, List.length_cons] at this ⊢
      omega

/-- **Every entry an indexed fold holds began before the World it reached** (HOST-53), when every
step moves the mark's step count (`hmono`; at the deployed instance `foldStep_steps`): the entry of
a record is the mark BEFORE it, and the fold only moves on. The World's step count never falls. -/
theorem indexed_foldlM_steps (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1) :
    ∀ (rs : List ByteArray) (w : W) (idx : Array Entry) (off : Nat) {st : W × Array Entry × Nat},
      rs.foldlM (indexed mark step) (w, idx, off) = .ok st →
      (∀ e ∈ idx.toList, e.steps < (mark w).1) →
      (mark w).1 ≤ (mark st.1).1 ∧ ∀ e ∈ st.2.1.toList, e.steps < (mark st.1).1
  | [], w, idx, off, st, h, hi => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨Nat.le_refl _, hi⟩
  | r :: rs, w, idx, off, st, h, hi => by
    simp only [List.foldlM] at h
    cases hs : step w r with
    | error e => simp [indexed, hs, bind, Except.bind] at h
    | ok w' =>
      have hlt := hmono w r w' hs
      rcases hm : mark w with ⟨a, ch⟩
      rw [hm] at hlt hi
      simp only [indexed, hs, hm, bind, Except.bind, pure, Except.pure] at h
      have hi' : ∀ e ∈ (idx.push ⟨a, off, ch⟩).toList, e.steps < (mark w').1 := by
        intro e he
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact Nat.lt_trans (hi e he) hlt
        · exact hlt
      obtain ⟨hle, hall⟩ := indexed_foldlM_steps mark step hmono rs w' _ _ h hi'
      exact ⟨by simp only at hlt ⊢; omega, hall⟩

/-- An indexed open of a tail from offset `off₀` ends its fold at `off₀ + validLen`: the offset the
next record's entry names is where the valid bytes end. -/
theorem openLog_indexed_off (s : Sealer) (m : Nat) (mark : W → Nat × ByteArray)
    (step : W → ByteArray → Except F W) (w : W) (idx : Array Entry) (off₀ : Nat) (initial tail : ByteArray)
    {op : Opened (W × Array Entry × Nat)}
    (h : openLog s m (indexed mark step) (w, idx, off₀) initial tail = .ok op) :
    op.world.2.2 = off₀ + op.validLen := by
  obtain ⟨rs, he, hf, _, _⟩ := open_sound s (indexed mark step) _ _ _ h
  have hv := openLog_validLen_le h
  have := congrArg ByteArray.size he
  rw [size_extract, size_encodeAll_sum] at this
  rw [indexed_foldlM_off mark step rs w idx off₀ hf]
  omega

/-! ## The one open over bytes -/

/-- The segment reads of the one open, over bytes: the base's tag and the tail are one range ending
at the segment's end. -/
theorem tail_read (S : ByteArray) {off len : Nat} (ht : tagBytes ≤ off) (hs : off + len = S.size) :
    (S.extract (off - tagBytes) (off - tagBytes + (tagBytes + len))).size = tagBytes + len ∧
    (S.extract (off - tagBytes) (off - tagBytes + (tagBytes + len))).extract 0 tagBytes =
      S.extract (off - tagBytes) off ∧
    (S.extract (off - tagBytes) (off - tagBytes + (tagBytes + len))).extract tagBytes
      (S.extract (off - tagBytes) (off - tagBytes + (tagBytes + len))).size = S.extract off S.size := by
  have e : off - tagBytes + (tagBytes + len) = S.size := by omega
  rw [e]
  refine ⟨by simp; omega, ?_, ?_⟩
  · rw [extract_extract]; congr 1 <;> omega
  · rw [extract_extract]; simp only [size_extract]; congr 1 <;> omega

theorem openWith_seg_ok (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o) :
    ∃ (b : Base W) (baseBytes : Nat) (digest : ByteArray) (len : Nat)
      (op : Opened (W × Array Entry × Nat)) (tag : Codec.Digest),
      Base.read keys c world file = .ok (b, baseBytes, digest) ∧
      tailRead c baseBytes b.offset S.size = .ok len ∧
      tagBytes ≤ b.offset ∧
      S.extract (b.offset - tagBytes) b.offset = b.tag.bytes ∧
      originFault (F := F) keys.segment (S.extract 0 (originLen b.offset)) (origin b.world) = none ∧
      b.indexCount ≤ indexMax ∧ b.indexCount * entryBytes keys ≤ I.size ∧
      indexNamed (keys.forStore (origin b.world)) b.indexCount b.indexLast (mark b.world).1
        (I.extract (lastAt keys b.indexCount).1 ((lastAt keys b.indexCount).1 + (lastAt keys b.indexCount).2)) = none ∧
      openLog keys.segment c.recordBytesMax (indexed mark step) (b.world, #[], b.offset) b.tag.bytes
        (S.extract b.offset S.size) = .ok op ∧
      Codec.Digest.ofBytes? op.lastTag = some tag ∧
      o = ⟨⟨op.world.1, op.records, op.validLen, op.lastTag, op.torn⟩,
        ⟨b.offset, baseBytes, (mark b.world).1, (mark b.world).2, digest, ⟨b.indexCount, b.indexLast⟩⟩,
          ⟨b.offset + op.validLen, tag⟩, op.world.2.1, I.size - b.indexCount * entryBytes keys⟩ := by
  unfold openWith at h
  simp only [segReader, pure_bind, Nat.zero_add] at h
  split at h
  · exact absurd h (by simp [Id.run, pure])
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i b baseBytes digest hb
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i len hlen
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i hoff
  have ⟨r1, r2, r3⟩ := tail_read S (Nat.le_of_not_lt hoff) hs
  rw [if_neg (by rw [r1]; simp)] at h
  rw [r2] at h
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i htag
  have hol : originLen b.offset ≤ S.size := by unfold originLen; omega
  rw [if_neg (by simp; omega)] at h
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i hof
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i hw
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i hi
  have hla := lastAt_within keys b.indexCount
  rw [if_neg (by simp; omega)] at h
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i hix
  rw [r3] at h
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i op hop
  split at h
  · exact absurd h (by simp [Id.run, pure])
  rename_i tag htg
  simp only [Id.run, pure, Except.ok.injEq] at h
  exact ⟨b, baseBytes, digest, len, op, tag, hb, hlen, by omega, by simpa using htag, hof,
    by omega, by omega, hix, hop, htg, h.symm⟩

/-- What `Base.read` decodes (HOSTING-4's ask): the base file's one frame verifies under the base
sealer, its head is the running shape stamp, and the base is the base codec's decode of the rest. -/
theorem Base.read_decode (keys : Keys) (c : Cadence) (world : Codec.Stream W) (file : ByteArray)
    {b : Base W} {n : Nat} {d : ByteArray} (h : Base.read keys c world file = .ok (b, n, d)) :
    ∃ r, frameAt keys.base c.baseRecordMax file 0 baseInitial = some r ∧
      r.record.extract 0 stampBytes = keys.shapes.bytes ∧
      (Base.codec world).decode (r.record.extract stampBytes r.record.size) = .ok b ∧
      n = world.size b.world := by
  unfold Base.read at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i r hr
  split at h
  · cases h
  dsimp only at h
  by_cases hs : r.record.extract 0 stampBytes = keys.shapes.bytes
  · rw [if_neg (by simpa using hs)] at h
    cases hb : (Base.codec world).decode (r.record.extract stampBytes r.record.size) with
    | error e => rw [hb] at h; cases h
    | ok b' =>
      rw [hb] at h
      cases h
      exact ⟨r, hr, hs, hb, rfl⟩
  · rw [if_pos hs] at h; cases h

/-- **The World an open reaches** (the pure half of `Host.openAt`, HOSTING-4's ask): the base
`Base.read` decodes from the base file, folded by `step` over records of the segment after it.
`openAt` is this `openWith` over the files' readers. -/
theorem openWith_world (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o) :
    ∃ (b : Base W) (baseBytes : Nat) (digest : ByteArray) (rs : List ByteArray),
      Base.read keys c world file = .ok (b, baseBytes, digest) ∧ rs.foldlM step b.world = .ok o.opened.world ∧
      o.opened.records = rs.length ∧ tagBytes ≤ b.offset ∧ o.sealed.offset = b.offset ∧
      (S.extract b.offset S.size).extract 0 (o.pos.offset - b.offset) =
        encodeAll keys.segment b.tag.bytes rs := by
  obtain ⟨b, baseBytes, digest, _, op, _, hb, _, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file I S h
  obtain ⟨rs, he, hf, _, hn⟩ := open_sound keys.segment (indexed mark step) _ _ _ hop
  refine ⟨b, baseBytes, digest, rs, hb, indexed_foldlM_fst mark step rs _ _ _ hf, hn, by omega, rfl, ?_⟩
  rw [show b.offset + op.validLen - b.offset = op.validLen by omega]
  exact he

/-- **The loop holds only the entries since the base** (HOST-33 condition 2: RAM O(tail), not
O(records)). An open that succeeds holds exactly one entry per record of the tail after its base,
and none of the base's own (those stay on disk, `sealed.index.count` of them); the loop's state
starts from it (`Opening.resident`) and `Resident.install` drops the entries each new base counts. -/
theorem openWith_tail_entries (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o) :
    o.index.size = o.opened.records := by
  obtain ⟨b, baseBytes, digest, _, op, _, hb, _, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file I S h
  obtain ⟨rs, _, hf, _, hn⟩ := open_sound keys.segment (indexed mark step) _ _ _ hop
  have := indexed_foldlM_size mark step rs _ _ _ hf
  simp only at this ⊢
  rw [this, hn]; simp

theorem lastTag_size (s : Sealer) : ∀ (prev : ByteArray) (rs : List ByteArray), prev.size = tagBytes →
    (lastTag s prev rs).size = tagBytes
  | _, [], h => h
  | _, _ :: rs, _ => lastTag_size s _ rs (s.tag_size _)

theorem extract_append_to_end (S y : ByteArray) {off : Nat} (h : off ≤ S.size) :
    (S ++ y).extract off (S ++ y).size = S.extract off S.size ++ y := by
  rw [extract_eq_extract_append_extract S.size h (by rw [size_append]; omega),
    extract_append_le (Nat.le_refl _), extract_append_eq_right rfl (size_append ..)]

/-- **What a live backup opens to (HOST-32).** `file`, `I`, `S` are `base.world`, `index.log` and
`seg.log` as they stood when the backup copied `base.world`, and that Store opens (the writer's
invariant). The backup holds that `file` and the append-only files with whatever was appended
since (`I ++ x`, `S ++ y`: `Store.backupOrder` copies them after the base). Then its open `R` is
either the same base with at least the live records, its World and index the live ones advanced by
the extra records' fold, ending no earlier; or a refusal by name: `tailTooLong` (the copy ran
past a later seal and its tail: the tail it names is past the bound
it names, HOST-55), `corrupt`, or `record j` at a record past the live ones. Never a
shorter open, and never `indexShort`/`indexCorrupt`/`foreignSegment`/`foreignOrigin`/`tagWidth`/
`shortRead`. The fold runs from the live state at the live position and ends at the backup's
position (the extra records' index entries name their true offsets), and a `corrupt` refusal
names bytes at or past the live position, never inside what the live Store opened. -/
theorem openWith_backup (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file I S x y : ByteArray)
    {o : Opening W} {R : Except (StoreFault F) (Opening W)}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o)
    (hR : Id.run (openWith keys c world mark origin step file (S ++ y).size (I ++ x).size
      (segReader (I ++ x)) (segReader (S ++ y))) = R) :
    (∃ o' more, R = .ok o' ∧ o'.sealed = o.sealed ∧
      o'.opened.records = o.opened.records + more.length ∧ o.pos.offset ≤ o'.pos.offset ∧
      foldRecords (indexed mark step) (o.opened.world, o.index, o.pos.offset) o.opened.records more =
        .ok (o'.opened.world, o'.index, o'.pos.offset)) ∨
    (∃ n mx, R = .error (.base (.tailTooLong n mx)) ∧ mx < n) ∨
    (∃ off, R = .error (.log (.corrupt off)) ∧ o.pos.offset ≤ off) ∨
    (∃ j f, R = .error (.log (.record j f)) ∧ o.opened.records ≤ j) := by
  have hfile : ¬ frameMax c.baseRecordMax < file.size := by
    intro hf; unfold openWith at h; rw [if_pos hf] at h; exact absurd h (by simp [Id.run, pure])
  obtain ⟨b, baseBytes, digest, len, op, tag, hb, hlen, hoff, htag, hof, hw, hi, hix, hop, htg, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file I S h
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  subst hR
  unfold openWith
  simp only [segReader, pure_bind, Nat.zero_add]
  rw [if_neg hfile, hb]
  dsimp only
  cases htr : tailRead c baseBytes b.offset (S ++ y).size with
  | error e =>
    refine Or.inr (Or.inl ?_)
    unfold tailRead at htr
    rw [if_neg (by rw [size_append]; omega)] at htr
    split at htr
    · rename_i hgt; cases htr; exact ⟨_, _, rfl, hgt⟩
    · cases htr
  | ok len' =>
    obtain ⟨hs', _⟩ := tailRead_ok htr
    have ⟨q1, q2, q3⟩ := tail_read (S ++ y) hoff hs'
    have hol : originLen b.offset ≤ S.size := by unfold originLen; omega
    dsimp only
    rw [if_neg (by omega), if_neg (by rw [q1]; simp), q2, extract_append_le (by omega),
      if_neg (by simpa using htag), if_neg (by simp [size_append]; omega), extract_append_le hol, hof]
    dsimp only
    have hla := lastAt_within keys b.indexCount
    rw [if_neg (by omega), if_neg (by rw [size_append]; omega), if_neg (by simp [size_append]; omega),
      extract_append_le (by omega), hix]
    dsimp only
    rw [q3, extract_append_to_end S y (by omega)]
    rcases openLog_append keys.segment c.recordBytesMax (indexed mark step) (b.world, #[], b.offset)
        b.tag.bytes _ y hop with ⟨o', more, ho', hfold, hrec, hvl⟩ | ⟨off, ho', hoffc⟩ | ⟨j, f, ho', hj⟩
    · rw [ho']
      obtain ⟨rs, _, _, hlt, _⟩ := open_sound keys.segment (indexed mark step) _ _ _ ho'
      have hsz : o'.lastTag.size = 32 := by
        rw [hlt]; exact lastTag_size keys.segment _ rs (Codec.Digest.size_eq _)
      dsimp only
      rw [show Codec.Digest.ofBytes? o'.lastTag = some ⟨o'.lastTag, hsz⟩ by
        simp [Codec.Digest.ofBytes?, hsz]]
      have e1 := openLog_indexed_off keys.segment c.recordBytesMax mark step b.world #[] b.offset _ _ hop
      have e2 := openLog_indexed_off keys.segment c.recordBytesMax mark step b.world #[] b.offset _ _ ho'
      refine Or.inl ⟨_, more, rfl, rfl, hrec, by simp only; omega, ?_⟩
      have hst : op.world = (op.world.1, op.world.2.1, b.offset + op.validLen) := by rw [← e1]
      have hst' : o'.world = (o'.world.1, o'.world.2.1, b.offset + o'.validLen) := by rw [← e2]
      rw [hst, hst'] at hfold
      simpa using hfold
    · rw [ho']
      exact Or.inr (Or.inr (Or.inl ⟨_, rfl, show b.offset + op.validLen ≤ b.offset + off by omega⟩))
    · rw [ho']
      exact Or.inr (Or.inr (Or.inr ⟨j, f, rfl, hj⟩))

/-! ## A restart between copies: the valid-prefix cut -/

theorem lenAt_lt {log : ByteArray} {off n : Nat} (h : lenAt log off = some n) : n < 2 ^ 32 := by
  unfold lenAt at h
  split at h
  · rename_i v _ _
    cases h
    exact UInt32.toNat_lt v
  · cases h

/-- A record `frameAt` reads fits its bound and a `u32` length field. -/
theorem frameAt_record_size {s : Sealer} {m : Nat} {log : ByteArray} {off : Nat} {prev : ByteArray}
    {rd : Read} (h : frameAt s m log off prev = some rd) : rd.record.size ≤ m ∧ rd.record.size < 2 ^ 32 := by
  unfold frameAt at h
  split at h
  · cases h
  · rename_i len hlen
    have h32 := lenAt_lt hlen
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hm hfit
        dsimp only at h
        split at h
        · cases h
          simp only [size_extract]
          omega
        · cases h

theorem go_record_size (s : Sealer) (m : Nat) (log : ByteArray) :
    ∀ (fuel off : Nat) (prev : ByteArray) (acc : List ByteArray),
      (∀ r ∈ acc, r.size ≤ m ∧ r.size < 2 ^ 32) →
      ∀ r ∈ (go s m log fuel off prev acc).records, r.size ≤ m ∧ r.size < 2 ^ 32 := by
  intro fuel
  induction fuel with
  | zero => intro off prev acc ha r hr; simp only [go, List.mem_reverse] at hr; exact ha r hr
  | succ fuel ih =>
    intro off prev acc ha
    simp only [go]
    split
    · intro r hr; simp only [List.mem_reverse] at hr; exact ha r hr
    · rename_i r₀ o t hstep
      apply ih o t (r₀ :: acc)
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · unfold step at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · rename_i rd hrd
            cases hstep
            exact frameAt_record_size hrd
          · cases hstep
      · exact ha r hr

/-- `open_sound`, with the bounds a recovered record meets (what `open_encodeAll` asks). -/
theorem open_sound_bounded (s : Sealer) {m : Nat} (step : W → ByteArray → Except F W) (w₀ : W)
    (initial log : ByteArray) {o : Opened W} (h : openLog s m step w₀ initial log = .ok o) :
    ∃ rs : List ByteArray, log.extract 0 o.validLen = encodeAll s initial rs ∧
      rs.foldlM step w₀ = .ok o.world ∧ o.lastTag = lastTag s initial rs ∧ o.records = rs.length ∧
      ∀ r ∈ rs, r.size ≤ m ∧ r.size < 2 ^ 32 := by
  obtain ⟨he, ht⟩ := encodeAll_recover s m initial log
  have hb := go_record_size s m log (log.size + 1) 0 initial [] (by simp)
  unfold openLog at h
  unfold recover at he ht
  unfold recover at h
  generalize go s m log (log.size + 1) 0 initial [] = rv at h he ht hb
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i w hw
      cases h
      exact ⟨rv.records, he, (foldRecords_ok step rv.records w₀ w 0).mp hw, ht, rfl, hb⟩
    · cases h

theorem extract_prefix (S : ByteArray) {n i j : Nat} (h : j ≤ n) :
    (S.extract 0 n).extract i j = S.extract i j := by
  rw [extract_extract]; congr 1 <;> omega

/-- **The cut a restart leaves opens to the same Store, clean.** If `file`, `I`, `S` open to `o`,
then the files cut to `o`'s valid end (`S.extract 0 o.pos.offset`: no torn tail) and to the
entries its base counts (`I.extract 0 (count * entryBytes)`: no orphans) open to `o` with
`torn = 0` and `orphan = 0`: every read the open makes lies inside the cut. -/
theorem openWith_cut (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o) :
    Id.run (openWith keys c world mark origin step file (S.extract 0 o.pos.offset).size
      (I.extract 0 (o.sealed.index.count * entryBytes keys)).size
      (segReader (I.extract 0 (o.sealed.index.count * entryBytes keys)))
      (segReader (S.extract 0 o.pos.offset))) =
      .ok { o with opened := { o.opened with torn := 0 }, orphan := 0 } := by
  have hfile : ¬ frameMax c.baseRecordMax < file.size := by
    intro hf; unfold openWith at h; rw [if_pos hf] at h; exact absurd h (by simp [Id.run, pure])
  obtain ⟨b, baseBytes, digest, len, op, tag, hb, hlen, hoff, htag, hof, hw, hi, hix, hop, htg, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file I S h
  obtain ⟨hs, hmax⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  dsimp only
  have hS' : (S.extract 0 (b.offset + op.validLen)).size = b.offset + op.validLen := by
    simp only [size_extract]; omega
  have hI' : (I.extract 0 (b.indexCount * entryBytes keys)).size = b.indexCount * entryBytes keys := by
    simp only [size_extract]; omega
  have htr : tailRead c baseBytes b.offset (S.extract 0 (b.offset + op.validLen)).size = .ok op.validLen := by
    unfold tailRead
    rw [hS', if_neg (by omega), if_neg (by omega)]
    congr 1; omega
  obtain ⟨rs, he, hf, hlt, hn, hrs⟩ := open_sound_bounded keys.segment (indexed mark step) _ _ _ hop
  have hes : (encodeAll keys.segment b.tag.bytes rs).size = op.validLen := by
    rw [← he]; simp only [size_extract]; omega
  have hcut : (S.extract 0 (b.offset + op.validLen)).extract b.offset
      (S.extract 0 (b.offset + op.validLen)).size = encodeAll keys.segment b.tag.bytes rs := by
    rw [hS', extract_prefix S (Nat.le_refl _), ← he, extract_extract]
    congr 1 <;> omega
  have hopc := open_encodeAll keys.segment (recordMax := c.recordBytesMax) (indexed mark step)
    (b.world, #[], b.offset) op.world b.tag.bytes rs hrs hf
  rw [hes, ← hlt, ← hn] at hopc
  have ⟨q1, q2, q3⟩ := tail_read (S.extract 0 (b.offset + op.validLen)) (len := op.validLen) hoff
    (by rw [hS'])
  have hol : originLen b.offset ≤ b.offset := by unfold originLen; omega
  have hla := lastAt_within keys b.indexCount
  unfold openWith
  simp only [segReader, pure_bind, Nat.zero_add]
  rw [if_neg hfile, hb]
  dsimp only
  rw [htr]
  dsimp only
  rw [if_neg (by omega), if_neg (by rw [q1]; simp), q2, extract_prefix S (by omega),
    if_neg (by simpa using htag), if_neg (by simp [hS']; omega), extract_prefix S (by omega), hof]
  dsimp only
  rw [if_neg (by omega), if_neg (by rw [hI']; omega), if_neg (by simp [hI']; omega),
    extract_prefix I (by omega), hix]
  dsimp only
  rw [q3, hcut, hopc]
  dsimp only
  rw [htg]
  simp only [Id.run, pure, hI', Nat.sub_self]

/-- **What a live backup opens to across writer restarts (HOST-32).** `file`, `I`, `S` are
`base.world`, `index.log` and `seg.log` as they stood when the backup copied `base.world`, and that
Store opens to `o`, having read only synced bytes (the writer's own opens do). The premise is
about bytes (the writer's invariant): `seg.log[0, o.pos.offset)` and
`index.log[0, o.sealed.index.count · entryBytes)` were durable when the backup copied `base.world`
and are never rewritten; a restart (`openWriter`) cuts only past its own open's valid end and
count, which are at or past these (a later base sits at or past the live valid end and counts at
least the live entries). So after any number of restarts and appends the later copies are the cut files
plus whatever was appended since: `S.extract 0 o.pos.offset ++ y` and
`I.extract 0 (o.sealed.index.count * entryBytes keys) ++ x`. The conclusion is `openWith_backup`'s:
the same base with at least the live records, or a refusal by name (`tailTooLong` past its bound, `corrupt` at or
past the live position, `record j` past the live records). It generalizes `openWith_backup`, whose
`S ++ y` is `S.extract 0 o.pos.offset ++ (S.extract o.pos.offset S.size ++ y)`. -/
theorem openWith_backup_restart (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file I S x y : ByteArray) {o : Opening W} {R : Except (StoreFault F) (Opening W)}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o)
    (hR : Id.run (openWith keys c world mark origin step file (S.extract 0 o.pos.offset ++ y).size
      (I.extract 0 (o.sealed.index.count * entryBytes keys) ++ x).size
      (segReader (I.extract 0 (o.sealed.index.count * entryBytes keys) ++ x))
      (segReader (S.extract 0 o.pos.offset ++ y))) = R) :
    (∃ o' more, R = .ok o' ∧ o'.sealed = o.sealed ∧
      o'.opened.records = o.opened.records + more.length ∧ o.pos.offset ≤ o'.pos.offset ∧
      foldRecords (indexed mark step) (o.opened.world, o.index, o.pos.offset) o.opened.records more =
        .ok (o'.opened.world, o'.index, o'.pos.offset)) ∨
    (∃ n mx, R = .error (.base (.tailTooLong n mx)) ∧ mx < n) ∨
    (∃ off, R = .error (.log (.corrupt off)) ∧ o.pos.offset ≤ off) ∨
    (∃ j f, R = .error (.log (.record j f)) ∧ o.opened.records ≤ j) := by
  have hb := openWith_backup keys c world mark origin step file _ _ x y
    (openWith_cut keys c world mark origin step file I S h) hR
  exact hb

end Nanodregg.Host
