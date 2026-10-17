/-
# Kernel.Proofs.Ledger — what the value receivers guarantee (LEDGER-3)

Conservation, floors and the cap are the KERNEL's (`Kernel.Proofs.Value`), for every turn. What
is proved here is the receive half: who may move value (`transfer_authorized`, the twin of
`write_authorized`), which value cells a receiver bears (`dispatch_value_born`: balance 0, and a
nonzero floor only from `issue`, equal to its signed cap, on the denomination it bears), and what
an admitted transfer does to the two accounts and nothing else (`transfer_exact`).
-/
import Kernel.Proofs.Value
import Codec.Proofs.Stream

namespace Nanodregg.Kernel

/-! ## A written touch, forward: what the World holds at it after admission -/

section Written
variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem mapEx_result_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {bs : List β}, mapEx f l = .ok bs → ∀ {a : α} {b : β}, a ∈ l → f a = .ok b → b ∈ bs
  | [], _, _, _, _, ha, _ => by simp at ha
  | x :: rest, bs, h, a, b, ha, hf => by
      unfold mapEx at h
      cases hx : f x with
      | error e => simp [hx] at h
      | ok r =>
          cases hr : mapEx f rest with
          | error e => simp [hx, hr] at h
          | ok rs =>
              simp only [hx, hr, Except.ok.injEq] at h
              subst h
              rcases List.mem_cons.mp ha with rfl | ha'
              · rw [hx] at hf; cases hf; simp
              · exact List.mem_cons_of_mem _ (mapEx_result_mem hr ha' hf)

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- The cells a turn's touches leave something at are a sublist of its touched cells. -/
theorem posts_sublist {E : Env D} {w : World D} :
    ∀ (l : List (Touch D)) (raw : List (Option (Post D))), mapEx (touchCheck E w) l = .ok raw →
      (raw.reduceOption.map Post.cell).Sublist (l.map Touch.cell)
  | [], raw, h => by simp [mapEx] at h; subst h; simp [List.reduceOption]
  | x :: rest, raw, h => by
      unfold mapEx at h
      cases hx : touchCheck E w x with
      | error e => simp [hx] at h
      | ok r =>
          cases hr : mapEx (touchCheck E w) rest with
          | error e => simp [hx, hr] at h
          | ok raw' =>
              simp only [hx, hr, Except.ok.injEq] at h
              subst h
              have ih := posts_sublist rest raw' hr
              cases r with
              | none =>
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons] at ih ⊢
                  exact ih.cons _
              | some p =>
                  have hp := (touchCheck_some hx).1
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons, hp] at ih ⊢
                  exact ih.cons_cons _

omit [DecidableEq D] in
theorem insertAll_get_of_mem {k : D} {e : Entry} :
    ∀ {m : Std.TreeMap D Entry compare} {ps : List (D × Entry)}, (ps.map Prod.fst).Nodup →
      (k, e) ∈ ps → (insertAll m ps)[k]? = some e
  | m, [], _, h => by simp at h
  | m, p :: rest, hn, h => by
      simp only [List.map_cons, List.nodup_cons] at hn
      show (insertAll (m.insert p.1 p.2) rest)[k]? = some e
      rcases List.mem_cons.mp h with rfl | h'
      · rw [insertAll_get_of_not_mem hn.1, Std.TreeMap.getElem?_insert_self]
      · exact insertAll_get_of_mem hn.2 h'

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem postWrite_eq {c : D} {cell post : Cell} {ops : List Op} (h : postWrite c cell ops = .ok post) :
    post = { cell with slots := applyOps cell.slots ops } := by
  unfold postWrite at h
  split at h
  · simp at h
  · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨_, _, _, _, h⟩ := h; exact h.symm
  · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨_, _, h⟩ := h; exact h.symm
  · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨_, _, _, _, h⟩ := h; exact h.symm

/-- **A written touch, forward.** An admitted turn that writes `ops` to a touched cell leaves
there exactly what `postWrite` makes of the cell it observed. -/
theorem admit_written {E : Env D} {w w' : World D} {t : Turn D} {x : Touch D} {ops : List Op}
    (h : World.admit E w t = .ok w') (hx : x ∈ t.touches) (ha : x.act = .write ops) :
    ∃ cell post, w.live x.cell = some cell ∧ postWrite x.cell cell ops = .ok post ∧
      w'.live x.cell = some post := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  obtain ⟨r, hr⟩ := mapEx_each hm x hx
  have hr' := hr
  unfold touchCheck at hr'
  simp only [except_bind_ok, ha] at hr'
  obtain ⟨⟨⟩, _, hr'⟩ := hr'
  cases hc : w.live x.cell with
  | none => rw [hc] at hr'; simp at hr'
  | some cell =>
      rw [hc] at hr'
      simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hr'
      obtain ⟨post, hp, hre⟩ := hr'
      refine ⟨cell, post, rfl, hp, ?_⟩
      rw [← hre] at hr
      have hin := mapEx_result_mem hm hx hr
      have hpost : (⟨x.cell, .live post, cell.weight + (ops.map Op.weight).sum - post.weight,
          flowsOf (some cell) (some post)⟩ : Post D) ∈ posts := by
        rw [hposts]; simpa [List.reduceOption, List.mem_filterMap] using hin
      have hshape := hk.shape
      unfold checkShape at hshape
      simp only [except_bind_ok] at hshape
      obtain ⟨⟨⟩, hnt, _⟩ := hshape
      have hnodup : ((posts.map Post.pair).map Prod.fst).Nodup := by
        rw [List.map_map]
        have : (Prod.fst ∘ Post.pair : Post D → D) = Post.cell := rfl
        rw [this, hposts]
        exact (posts_sublist t.touches raw hm).nodup (noDup_nodup hnt)
      have hcr := hk.creates
      unfold checkCreates at hcr
      simp only [except_bind_ok] at hcr
      obtain ⟨⟨⟩, _, ⟨⟩, hnbt, _⟩ := hcr
      have hnb : x.cell ∉ (bornEntries E t).map Prod.fst := by
        intro hm'
        unfold bornEntries createdPairs at hm'
        rw [List.map_map] at hm'
        have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2)) = Prod.fst := rfl
        rw [this, List.map_fst_zip (by simp [createdIds])] at hm'
        exact (List.nodup_append.mp (noDup_nodup hnbt)).2.2 _ (List.mem_map_of_mem hx) _ hm' rfl
      unfold World.live
      show (match (insertAll (insertAll w.cells (posts.map Post.pair)) (bornEntries E t))[x.cell]? with
        | some (.live cell) => some cell | _ => none) = some post
      rw [insertAll_get_of_not_mem hnb,
        insertAll_get_of_mem hnodup (List.mem_map_of_mem (f := Post.pair) hpost)]

end Written

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The slot codecs read back -/

theorem balanceOf_bytes {b : Int} (h : Value.fits b = true) : Value.balanceOf (Value.balanceBytes b) = some b := by
  unfold Value.balanceOf Value.balanceBytes
  rw [decode_bytes i64_lawful]
  have := of_decide_eq_true h
  simp only [Option.some.injEq]
  exact Int64.toInt_ofInt_of_le this.1 this.2

theorem floorOf_bytes (f : Nat) : Value.floorOf (Value.floorBytes f) = some (f % 2 ^ 64) := by
  unfold Value.floorOf Value.floorBytes
  rw [decode_bytes u64_lawful]
  simp

omit [Ord D] [DecidableEq D] in
/-- The account a ledger receiver bears holds denomination `d`, balance 0 and floor `f`
(modulo `2^64`, which `issue`'s cap bound makes exact). -/
theorem accountCell_value {X : Ctx D} {o : D} {d : ByteArray} {f : Nat} {v : Value}
    (h : Value.ofCell (accountCell X o d f) = some v) :
    v.denom = d ∧ v.balance = 0 ∧ v.floor = f % 2 ^ 64 := by
  have h8 : (accountCell X o d f).slots.get Value.denomKey = some d := by
    simp [accountCell, slotsOf_get, Value.denomKey, slotOwner, Value.balanceKey, Value.floorKey]
  have h9 : (accountCell X o d f).slots.get Value.balanceKey = some (Value.balanceBytes 0) := by
    simp [accountCell, slotsOf_get, Value.denomKey, slotOwner, Value.balanceKey, Value.floorKey]
  have h10 : (accountCell X o d f).slots.get Value.floorKey = some (Value.floorBytes f) := by
    simp [accountCell, slotsOf_get, Value.denomKey, slotOwner, Value.balanceKey, Value.floorKey]
  unfold Value.ofCell at h
  rw [if_pos (show (accountCell X o d f).discipline = .value from rfl), h8, h9, h10] at h
  simp only [Option.bind_some, balanceOf_bytes (b := 0) (by decide), floorOf_bytes] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩
  · simp at h

/-! ## Authority -/

omit [Ord D] [DecidableEq D] in
theorem readAccount_ok {look : Pinned D} {c : D} {cell : Cell} {v : Value}
    (h : readAccount look c = .ok (cell, v)) :
    readKind look c kindAccount = .ok cell ∧ Value.ofCell cell = some v := by
  unfold readAccount at h
  simp only [except_bind_ok] at h
  obtain ⟨cell', hk, h⟩ := h
  split at h
  · rename_i v' hv
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hk, hv⟩
  · simp at h

/-- **Transfer authority** (the twin of `write_authorized`). A derived transfer moves value out of
an account only for its owner: the signer, or an agent holding a grant chain for `mutate` on the
source whose root issuer is the owner. -/
theorem transfer_authorized {X : Ctx D} {look : Pinned D} {c : Call D} {src dst : D} {amount : Nat}
    {via : Option D} {once : Option ByteArray} {t : Turn D}
    (h : transfer X look c src dst amount via once = .ok t) :
    ∃ cell owner, readKind look src kindAccount = .ok cell ∧
      slotDigest X src cell slotOwner = .ok owner ∧
      (via = none ∧ c.unsigned.member = owner ∨
        ∃ g, via = some g ∧ Chain X look src .mutate g c.unsigned.member owner) := by
  unfold transfer at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨scell, sv⟩, hs, ⟨_, _⟩, _, principal, ha, _⟩ := h
  obtain ⟨hk, _⟩ := readAccount_ok hs
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, _⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨scell, p, hk, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g => right; exact ⟨g, rfl, walk_chain hp⟩

/-- **A transfer's once key is spent.** A derived transfer carries exactly the nullifier of its
once key (if it has one) in its source's namespace, so (`admit_nullifiers`) a transfer with the
same key from the same source lands at most once in the life of the World. Without a key, replay
protection is the transaction id's journal alone. -/
theorem transfer_once {X : Ctx D} {look : Pinned D} {c : Call D} {src dst : D} {amount : Nat}
    {via : Option D} {once : Option ByteArray} {t : Turn D}
    (h : transfer X look c src dst amount via once = .ok t) :
    t.nullifiers = (once.map (onceNullifier X src)).toList := by
  unfold transfer at h
  simp only [except_bind_ok] at h
  obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, h⟩ := h
  exact (sealTurn_ok h).2.2.2.2.2.2.2.2.1

/-! ## Births -/

omit [Ord D] [DecidableEq D] in
theorem ofCell_not_value {cell : Cell} (h : cell.discipline ≠ .value) : Value.ofCell cell = none := by
  unfold Value.ofCell; simp [h]

/-- **Which value cells a receiver bears.** Every born value cell has balance 0; its floor is 0
unless the call is `issue cap`, and then the floor IS the signed cap and the denomination is the
bytes of the turn's first born id: the well names itself. With `Kernel.Proofs.Value.admit_birth`
and `fold_floors_held`, the cap is the denomination's floor sum forever. -/
theorem dispatch_value_born {X : Ctx D} {look : Pinned D} {c : Call D} {b : Body D} {t : Turn D}
    (h : dispatch X look c b = .ok t) :
    ∀ cell ∈ t.creates, ∀ v, Value.ofCell cell = some v →
      v.balance = 0 ∧ (v.floor = 0 ∨ ∃ cap, b = .issue cap ∧ v.floor = cap ∧
        v.denom = X.env.bytes (cellIdOf X.env t.txId 0)) := by
  have notv : ∀ (cell : Cell) (cr : List Cell), cr = [cell] → cell.discipline ≠ .value →
      ∀ x ∈ cr, ∀ v, Value.ofCell x = some v → False := by
    intro cell cr hcr hd x hx v hv
    subst hcr; simp at hx; subst hx; rw [ofCell_not_value hd] at hv; cases hv
  cases b with
  | enroll key next possession via =>
      simp only [dispatch, enroll, except_bind_ok] at h
      obtain ⟨_, _, _, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]
      exact fun x hx v hv => (notv _ _ rfl (by simp) x hx v hv).elim
  | rotate key next =>
      simp only [dispatch, rotate, except_bind_ok] at h
      obtain ⟨_, _, ⟨⟩, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | install pkg =>
      simp only [dispatch, install, except_bind_ok] at h
      obtain ⟨⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]
      exact fun x hx v hv => (notv _ _ rfl (by simp) x hx v hv).elim
  | create pkg laws state =>
      simp only [dispatch, create, except_bind_ok] at h
      obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]
      exact fun x hx v hv => (notv _ _ rfl (by simp [objectCell]) x hx v hv).elim
  | write obj edits via =>
      simp only [dispatch, write, except_bind_ok] at h
      obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | law obj laws via =>
      simp only [dispatch, law, except_bind_ok] at h
      obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | invoke obj method args budget via =>
      simp only [dispatch, invoke, except_bind_ok] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | grant target grantee rights parent =>
      simp only [dispatch, grant, except_bind_ok] at h
      obtain ⟨_, _, _, _, h⟩ := h
      rw [sealTurn_creates h]
      exact fun x hx v hv => (notv _ _ rfl (by simp) x hx v hv).elim
  | revoke g =>
      simp only [dispatch, revoke, except_bind_ok] at h
      obtain ⟨_, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | issue cap =>
      simp only [dispatch, issue, except_bind_ok] at h
      obtain ⟨⟨⟩, hcap, h⟩ := h
      rw [req_ok, decide_eq_true_eq] at hcap
      have htx := (sealTurn_ok h).2.2.2.2.1
      rw [sealTurn_creates h]
      intro x hx v hv
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨hd, hb, hf⟩ := accountCell_value hv
      refine ⟨hb, .inr ⟨cap, rfl, ?_, by rw [hd, htx]⟩⟩
      rw [hf]; exact Nat.mod_eq_of_lt (by unfold capMax at hcap; omega)
  | account asset =>
      simp only [dispatch, account] at h
      rw [sealTurn_creates h]
      intro x hx v hv
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨_, hb, hf⟩ := accountCell_value hv
      exact ⟨hb, .inl (by rw [hf])⟩
  | transfer src dst amount via once =>
      simp only [dispatch, transfer, except_bind_ok] at h
      obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp

/-! ## What an admitted transfer does -/

/-- Setting a value cell's balance slot to an `i64` leaves its denomination and floor. -/
theorem ofCell_setBalance {cell : Cell} {v : Value} {b : Int} (hv : Value.ofCell cell = some v)
    (hb : Value.fits b = true) :
    Value.ofCell { cell with slots := applyOps cell.slots [.set Value.balanceKey (Value.balanceBytes b)] } =
      some { v with balance := b } := by
  have hd := ofCell_value hv
  unfold Value.ofCell at hv ⊢
  simp only [applyOps, List.foldl, applyOp, hd, if_true] at hv ⊢
  rw [slots_get_set_ne _ (by decide : Value.denomKey ≠ Value.balanceKey),
    slots_get_set_eq, slots_get_set_ne _ (by decide : Value.floorKey ≠ Value.balanceKey)]
  simp only [Option.bind_some, balanceOf_bytes hb]
  split at hv
  · rename_i dd bb ff h1 h2 h3
    rw [h1, h3]
    split at hv
    · simp only [Option.some.injEq] at hv; subst hv; simp_all
    · simp at hv
  · simp at hv

theorem pinned_live {w : World D} {pins : List (D × D)} {c : D} {cell : Cell}
    (h : pinned w pins c = .ok (some cell)) : w.live c = some cell := by
  unfold pinned at h; split at h
  · simpa using h
  · simp at h

section Exact
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **An admitted transfer moves exactly `amount`**, and nothing else: the source's balance falls
by it, the destination's rises by it, both keep their denomination and floor, and every other
cell is untouched (L1's `transfer_conserves`, on touches). -/
theorem transfer_exact {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {src dst : D}
    {amount : Nat} {via : Option D} {once : Option ByteArray}
    (hb : c.unsigned.body = .transfer src dst amount via once)
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') :
    ∃ sv dv, (w.live src).bind Value.ofCell = some sv ∧ (w.live dst).bind Value.ofCell = some dv ∧
      (w'.live src).bind Value.ofCell = some { sv with balance := sv.balance - amount } ∧
      (w'.live dst).bind Value.ofCell = some { dv with balance := dv.balance + amount } ∧
      ∀ k, k ≠ src → k ≠ dst → k ∉ createdIds X.env t → w'.cells[k]? = w.cells[k]? := by
  have hd := receiveWith_dispatch hr
  rw [hb] at hd
  simp only [dispatch, transfer, except_bind_ok] at hd
  obtain ⟨⟨scell, sv⟩, hs, ⟨dcell, dv⟩, hdd, _, _, ⟨⟩, hne, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hfs, ⟨⟩, hfd, hseal⟩ := hd
  rw [req_ok, decide_eq_true_eq] at hne
  rw [req_ok] at hfs hfd
  simp only at hfs hfd hseal
  obtain ⟨hks, hvs⟩ := readAccount_ok hs
  obtain ⟨hkd, hvd⟩ := readAccount_ok hdd
  have hls := pinned_live (readKind_ok hks).1
  have hld := pinned_live (readKind_ok hkd).1
  obtain ⟨_, _, htouch, _, _, _, _, _, _, hpin⟩ := sealTurn_ok hseal
  let efs : List (D × Act) := [(src, setBalance (sv.balance - amount)), (dst, setBalance (dv.balance + amount))]
  have hact : ∀ k, actFor efs k = if k = src then setBalance (sv.balance - amount)
      else if k = dst then setBalance (dv.balance + amount) else .keep := by
    intro k
    unfold actFor
    by_cases h1 : src = k
    · subst h1; simp [efs]
    · by_cases h2 : dst = k
      · subst h2; simp [efs, h1, Ne.symm h1]
      · simp [efs, h1, h2, Ne.symm h1, Ne.symm h2]
  -- the touch at a pinned effect cell writes its balance
  have written : ∀ k b, (k, setBalance b) ∈ efs → actFor efs k = setBalance b →
      ∃ cell post, w.live k = some cell ∧
        postWrite k cell [.set Value.balanceKey (Value.balanceBytes b)] = .ok post ∧ w'.live k = some post := by
    intro k b hm hk
    obtain ⟨p, hp, hpk⟩ := hpin _ hm
    have hx : ({ cell := p.1, seen := p.2, act := actFor efs p.1 } : Touch D) ∈ t.touches := by
      rw [htouch]; exact List.mem_map_of_mem hp
    simp only at hpk
    rw [hpk] at hx
    exact admit_written ha hx (by simp only; rw [hk]; rfl)
  obtain ⟨c1, p1, hc1, hw1, hl1⟩ := written src (sv.balance - amount) (by simp [efs]) (by rw [hact]; simp)
  obtain ⟨c2, p2, hc2, hw2, hl2⟩ := written dst (dv.balance + amount) (by simp [efs]) (by rw [hact]; simp [Ne.symm hne])
  rw [hls] at hc1; cases hc1
  rw [hld] at hc2; cases hc2
  refine ⟨sv, dv, by rw [hls]; exact hvs, by rw [hld]; exact hvd, ?_, ?_, ?_⟩
  · rw [hl1, postWrite_eq hw1]; exact ofCell_setBalance hvs hfs
  · rw [hl2, postWrite_eq hw2]; exact ofCell_setBalance hvd hfd
  · intro k h1 h2 hc
    refine admit_frame ha (fun x hx hxk => ?_) hc
    rw [htouch] at hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    simp only at hxk ⊢
    rw [hact, if_neg (hxk ▸ h1), if_neg (hxk ▸ h2)]

end Exact

end Nanodregg.Kernel.Receive
