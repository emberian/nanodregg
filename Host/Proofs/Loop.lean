/-
# Host.Proofs.Loop — a batch cut neither drops, duplicates nor reorders a frame (D4)

`drainM` is the loop's batch cut, generic in the monad. Over a list model of the port (`poll` pops
the front, `unread` pushes a frame back on the front), the batch followed by what the port still
holds is exactly the first frame followed by what the port held: every frame the loop took is in
the batch or back in the port, in arrival order, and the batch is never empty. Since the loop
holds nothing between batches but the port (`serve` takes no carried frame), a round may end
`fuel` at any batch boundary and the next round, on the same port, sees every frame not yet
batched: no accepted frame is lost across a restart.
-/
import Host.Loop

namespace Nanodregg.Host

/-- The list model of a port's queue: `poll` pops the front. (Private: a proof module exports no
definitions, closure C3.) -/
private def listPoll : StateM (List Frame) (Option Frame) :=
  modifyGet fun | [] => (none, []) | f :: q => (some f, q)

/-- `unread` pushes a frame back on the front. -/
private def listUnread (f : Frame) : StateM (List Frame) Unit :=
  modify (f :: ·)

/-! The four ways one step of the cut goes, over the list model. -/

theorem go_full (limits : Limits) (n : Nat) (acc : Array Frame) (bytes : Nat) (q : List Frame)
    (hm : limits.batchMax ≤ acc.size) :
    (drainM.go listPoll listUnread limits (n + 1) acc bytes).run q = (acc, q) := by
  simp only [drainM.go, hm, if_true]; rfl

theorem go_empty (limits : Limits) (n : Nat) (acc : Array Frame) (bytes : Nat)
    (hm : ¬ limits.batchMax ≤ acc.size) :
    (drainM.go listPoll listUnread limits (n + 1) acc bytes).run [] = (acc, []) := by
  simp only [drainM.go, hm, if_false]; rfl

theorem go_over (limits : Limits) (n : Nat) (acc : Array Frame) (bytes : Nat) (f : Frame)
    (q : List Frame) (hm : ¬ limits.batchMax ≤ acc.size)
    (hb : limits.batchBytesMax < bytes + f.payload.size) :
    (drainM.go listPoll listUnread limits (n + 1) acc bytes).run (f :: q) = (acc, f :: q) := by
  simp only [drainM.go, hm, if_false]
  change (if limits.batchBytesMax < bytes + f.payload.size then
      (listUnread f *> pure acc : StateM (List Frame) (Array Frame)) else _).run q = _
  rw [if_pos hb]; rfl

theorem go_take (limits : Limits) (n : Nat) (acc : Array Frame) (bytes : Nat) (f : Frame)
    (q : List Frame) (hm : ¬ limits.batchMax ≤ acc.size)
    (hb : ¬ limits.batchBytesMax < bytes + f.payload.size) :
    (drainM.go listPoll listUnread limits (n + 1) acc bytes).run (f :: q) =
      (drainM.go listPoll listUnread limits n (acc.push f) (bytes + f.payload.size)).run q := by
  simp only [drainM.go, hm, if_false]
  change (if limits.batchBytesMax < bytes + f.payload.size then _ else
      (pure PUnit.unit >>= fun _ =>
        drainM.go listPoll listUnread limits n (acc.push f) (bytes + f.payload.size) :
          StateM (List Frame) (Array Frame))).run q = _
  rw [if_neg hb]; rfl

/-- The cut's invariant: what it returns followed by what it leaves is what it held followed by the
port; it only grows the batch; and it grows it to at most `max 1 batchMax` frames. -/
theorem drainM_go_conserves (limits : Limits) (fuel : Nat) (acc : Array Frame) (bytes : Nat)
    (q : List Frame) :
    ((drainM.go listPoll listUnread limits fuel acc bytes).run q).1.toList ++
        ((drainM.go listPoll listUnread limits fuel acc bytes).run q).2 = acc.toList ++ q ∧
      acc.size ≤ ((drainM.go listPoll listUnread limits fuel acc bytes).run q).1.size ∧
      (acc.size ≤ max 1 limits.batchMax →
        ((drainM.go listPoll listUnread limits fuel acc bytes).run q).1.size ≤ max 1 limits.batchMax) := by
  induction fuel generalizing acc bytes q with
  | zero => exact ⟨rfl, Nat.le_refl _, id⟩
  | succ n ih =>
    by_cases hm : limits.batchMax ≤ acc.size
    · rw [go_full limits n acc bytes q hm]; exact ⟨rfl, Nat.le_refl _, id⟩
    · cases q with
      | nil => rw [go_empty limits n acc bytes hm]; exact ⟨rfl, Nat.le_refl _, id⟩
      | cons f q =>
        by_cases hb : limits.batchBytesMax < bytes + f.payload.size
        · rw [go_over limits n acc bytes f q hm hb]; exact ⟨rfl, Nat.le_refl _, id⟩
        · rw [go_take limits n acc bytes f q hm hb]
          obtain ⟨h1, h2, h3⟩ := ih (acc.push f) (bytes + f.payload.size) q
          have hsz : (acc.push f).size = acc.size + 1 := Array.size_push ..
          refine ⟨by rw [h1]; simp, by omega, fun _ => h3 (by omega)⟩

/-- **No frame lost, duplicated or reordered by a batch cut**; the batch is never empty and holds
at most `max 1 batchMax` frames. -/
theorem drainM_conserves (limits : Limits) (first : Frame) (q : List Frame) :
    ((drainM listPoll listUnread limits first).run q).1.toList ++
        ((drainM listPoll listUnread limits first).run q).2 = first :: q ∧
      0 < ((drainM listPoll listUnread limits first).run q).1.size ∧
      ((drainM listPoll listUnread limits first).run q).1.size ≤ max 1 limits.batchMax := by
  have := drainM_go_conserves limits limits.batchMax #[first] first.payload.size q
  simp only [drainM]
  exact ⟨by simpa using this.1, by simpa using this.2.1, this.2.2 (by simp; exact Nat.le_max_left 1 _)⟩

/-- The payload bytes of a batch. -/
private def payloadBytes (fs : Array Frame) : Nat := (fs.toList.map (·.payload.size)).sum

/-- The cut's byte invariant: it never takes a frame that would carry the batch's payload past the
bound, so a batch that started within `M` (any bound at least `batchBytesMax`) ends within it. -/
theorem drainM_go_bytes (limits : Limits) (M : Nat) (hM : limits.batchBytesMax ≤ M) (fuel : Nat)
    (acc : Array Frame) (bytes : Nat) (q : List Frame)
    (hacc : payloadBytes acc = bytes) (hb : bytes ≤ M) :
    payloadBytes ((drainM.go listPoll listUnread limits fuel acc bytes).run q).1 ≤ M := by
  induction fuel generalizing acc bytes q with
  | zero => change payloadBytes acc ≤ M; omega
  | succ n ih =>
    by_cases hm : limits.batchMax ≤ acc.size
    · rw [go_full limits n acc bytes q hm]; change payloadBytes acc ≤ M; omega
    · cases q with
      | nil => rw [go_empty limits n acc bytes hm]; change payloadBytes acc ≤ M; omega
      | cons f q =>
        by_cases hbo : limits.batchBytesMax < bytes + f.payload.size
        · rw [go_over limits n acc bytes f q hm hbo]; change payloadBytes acc ≤ M; omega
        · rw [go_take limits n acc bytes f q hm hbo]
          refine ih (acc.push f) (bytes + f.payload.size) q ?_ (by omega)
          simp [payloadBytes, ← hacc]

/-- **A batch's payload stays within `batchBytesMax`**, or is its first frame alone (the first frame
is always taken, so a single frame larger than the bound is a batch of one): the frames after the
first never carry it past the bound (OPS's law-6 read of D4). -/
theorem drainM_bytes (limits : Limits) (first : Frame) (q : List Frame) :
    payloadBytes ((drainM listPoll listUnread limits first).run q).1 ≤
      max first.payload.size limits.batchBytesMax := by
  simp only [drainM]
  exact drainM_go_bytes limits _ (Nat.le_max_right _ _) _ _ _ q (by simp [payloadBytes])
    (Nat.le_max_left _ _)

/-- **The top loop is total and its exhaustion exits by name** (LAW 4 as amended, HOST-19): with
its round budget spent, `restarts` runs no round and ends `Exit.lifetime` (class restart, never
silent), holding the state it was given. -/
theorem restarts_spent {W : Type} (round : Resident W → IO (Exit × Resident W))
    (reopen : IO (Except Exit (Resident W))) (mark : W → Nat × ByteArray) (r : Resident W) :
    restarts round reopen mark 0 r = pure (.lifetime, r) := rfl

end Nanodregg.Host
