/-
# Kernel.Proofs.Ledger — what the value receivers guarantee (LEDGER-3)

Conservation, floors and the cap are the KERNEL's (`Kernel.Proofs.Value`), for every turn. What
is proved here is the receive half: who may move value (`transfer_authorized`, the twin of
`write_authorized`), which value cells a receiver bears (`dispatch_value_born`: balance 0, and a
nonzero floor only from `issue`, equal to its signed cap, on the denomination it bears), and what
an admitted transfer does to the two accounts and nothing else (`transfer_exact`).
-/
import Kernel.Proofs.Value
import Kernel.Proofs.Origin
import Kernel.Proofs.Tree
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

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem insertAll_get_of_mem {E : Env D} {k : D} {e : Entry} :
    ∀ {m : Cells D} {ps : List (D × Entry)}, (ps.map Prod.fst).Nodup →
      (k, e) ∈ ps → (insertAll E m ps).get (trieSpec E) (.cell k) = some (.entry e)
  | m, [], _, h => by simp at h
  | m, p :: rest, hn, h => by
      simp only [List.map_cons, List.nodup_cons] at hn
      show (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).get _ _ = _
      rcases List.mem_cons.mp h with rfl | h'
      · rw [insertAll_get_of_not_mem hn.1, Trie.get_insert_self]
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
    ∃ cell post, w.live E x.cell = some cell ∧ postWrite x.cell cell ops = .ok post ∧
      w'.live E x.cell = some post := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  obtain ⟨r, hr⟩ := mapEx_each hm x hx
  have hr' := hr
  unfold touchCheck at hr'
  simp only [except_bind_ok, ha] at hr'
  obtain ⟨⟨⟩, _, hr'⟩ := hr'
  rcases hc : w.entry E x.cell with _ | ⟨cell, v⟩ | _
  · rw [hc] at hr'; simp at hr'
  · rw [hc] at hr'
    simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hr'
    obtain ⟨⟨⟩, _, post, hp, hre⟩ := hr'
    refine ⟨cell, post, by unfold World.live; rw [hc], hp, ?_⟩
    rw [← hre] at hr
    have hin := mapEx_result_mem hm hx hr
    have hpost : (⟨x.cell, .live post (v + 1), cell.weight + (ops.map Op.weight).sum - post.weight,
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
    obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, hnbt, _⟩ := hcr
    have hnb : x.cell ∉ (bornEntries t).map Prod.fst := by
      intro hm'
      unfold bornEntries at hm'
      rw [List.map_map] at hm'
      have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2 0)) = Prod.fst := rfl
      rw [this] at hm'
      exact (List.nodup_append.mp (noDup_nodup hnbt)).2.2 _ (List.mem_map_of_mem hx) _ hm' rfl
    apply get_live (v := v + 1)
    rw [show (commit E w t posts).trie = commitTrie E w t posts from rfl, commitTrie_cell,
      insertAll_get_of_not_mem hnb,
      insertAll_get_of_mem hnodup (List.mem_map_of_mem (f := Post.pair) hpost)]
  · rw [hc] at hr'; simp at hr'

/-- **A written touch, forward, by entry**: the observed cell at version `v`, the written one at `v + 1`
(KERNEL-60's `rotate_stales_outstanding` reads the version). -/
theorem admit_written_entry {E : Env D} {w w' : World D} {t : Turn D} {x : Touch D} {ops : List Op}
    (h : World.admit E w t = .ok w') (hx : x ∈ t.touches) (ha : x.act = .write ops) :
    ∃ cell v post, w.entry E x.cell = some (.live cell v) ∧ postWrite x.cell cell ops = .ok post ∧
      w'.entry E x.cell = some (.live post (v + 1)) := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  obtain ⟨r, hr⟩ := mapEx_each hm x hx
  have hr' := hr
  unfold touchCheck at hr'
  simp only [except_bind_ok, ha] at hr'
  obtain ⟨⟨⟩, _, hr'⟩ := hr'
  rcases hc : w.entry E x.cell with _ | ⟨cell, v⟩ | _
  · rw [hc] at hr'; simp at hr'
  · rw [hc] at hr'
    simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hr'
    obtain ⟨⟨⟩, _, post, hp, hre⟩ := hr'
    refine ⟨cell, v, post, rfl, hp, ?_⟩
    rw [← hre] at hr
    have hin := mapEx_result_mem hm hx hr
    have hpost : (⟨x.cell, .live post (v + 1), cell.weight + (ops.map Op.weight).sum - post.weight,
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
    obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, hnbt, _⟩ := hcr
    have hnb : x.cell ∉ (bornEntries t).map Prod.fst := by
      intro hm'
      unfold bornEntries at hm'
      rw [List.map_map] at hm'
      have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2 0)) = Prod.fst := rfl
      rw [this] at hm'
      exact (List.nodup_append.mp (noDup_nodup hnbt)).2.2 _ (List.mem_map_of_mem hx) _ hm' rfl
    unfold World.entry
    rw [show (commit E w t posts).trie = commitTrie E w t posts from rfl, commitTrie_cell,
      insertAll_get_of_not_mem hnb,
      insertAll_get_of_mem hnodup (List.mem_map_of_mem (f := Post.pair) hpost)]
  · rw [hc] at hr'; simp at hr'

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

theorem floorOf_lt {b : ByteArray} {f : Nat} (h : Value.floorOf b = some f) : f < 2 ^ 64 := by
  unfold Value.floorOf at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact UInt64.toNat_lt _
  · simp at h

/-- A decoded floor is a `u64`'s. -/
theorem ofCell_floor_lt {cell : Cell} {v : Value} (h : Value.ofCell cell = some v) : v.floor < 2 ^ 64 := by
  unfold Value.ofCell at h
  split at h
  · split at h
    · rename_i dd bb ff _ _ hf
      split at h
      · simp only [Option.some.injEq] at h; subst h
        cases hk : cell.slots.get Value.floorKey with
        | none => rw [hk] at hf; simp at hf
        | some b => rw [hk] at hf; exact floorOf_lt hf
      · simp at h
    · simp at h
  · simp at h

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

omit [Ord D] [DecidableEq D] in
/-- A reference reads the account at the id it resolves to; a `.well` reference only a well. -/
theorem readRef_ok {X : Ctx D} {look : Pinned D} {r : AcctRef D} {id : D} {cell : Cell} {v : Value}
    (h : readRef X look r = .ok (id, cell, v)) :
    id = r.resolve X ∧ readAccount look id = .ok (cell, v) ∧
      ∀ a, r = .well a → v.denom = X.env.bytes a := by
  unfold readRef at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨cell', v'⟩, hr, h⟩ := h
  cases r with
  | well a =>
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, hw, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [req_ok, decide_eq_true_eq] at hw
      exact ⟨rfl, hr, fun a' ha => by cases ha; exact hw⟩
  | of o a =>
      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hr, fun a' ha => by cases ha⟩

omit [DecidableEq D] in
/-- **One account per (owner, denomination)** (KERNEL-28 (d)): two pairs with one account id are
the same pair, or the two account inputs collide (`accountPre`; tooth `account_keyed_sep`). Over a lawful `Env` (digest bytes injective and
all of one size `n`, the deployed 32), the hash's input splits back into the owner and the
denomination. -/
theorem account_keyed {X : Ctx D} {n : Nat} (hE : X.env.Lawful n) {a s b t : D}
    (h : accountId X a s = accountId X b t) :
    (a, s) = (b, t) ∨ CollidesAmong X.env.hash [accountPre X a s, accountPre X b t] := by
  by_cases he : X.env.bytes a ++ X.env.bytes s = X.env.bytes b ++ X.env.bytes t
  · left
    obtain ⟨h1, h2⟩ := (ByteArray.append_eq_append_iff_of_size_eq_left
      (by rw [hE.size a, hE.size b])).mp he
    rw [hE.bytes_eq h1, hE.bytes_eq h2]
  · right
    exact .pair (fun e => he (congrArg Prod.snd e)) h

omit [DecidableEq D] in
/-- **Tooth of `account_keyed`**: where the hash separates the two account inputs, one account id
is one (owner, denomination). -/
theorem account_keyed_sep {X : Ctx D} {n : Nat} (hE : X.env.Lawful n) {a s b t : D}
    (hs : Separates X.env.hash [accountPre X a s, accountPre X b t])
    (h : accountId X a s = accountId X b t) : (a, s) = (b, t) :=
  hs.elim (account_keyed hE h)

omit [Ord D] [DecidableEq D] in
/-- **An account is born at its keyed id**, owned by the named owner, of the named denomination,
balance and floor 0; it bears nothing else and writes nothing. -/
theorem account_creates {X : Ctx D} {asset owner : D} {d : Draft D}
    (h : account X asset owner = .ok d) :
    d.creates = [(accountId X owner asset, accountCell X owner (X.env.bytes asset) 0)] ∧
      d.effects = [] ∧ d.nullifiers = [] := by
  simp only [account, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

omit [Ord D] [DecidableEq D] in
/-- What a use of a counted right through `via` spends (KERNEL-60): nothing for the owner's own
authority, else the pinned live grant's `spendAt`. -/
theorem spendVia_ok {look : Pinned D} {base : Nat} {via : Option D} {units : Nat} {short : D → Refusal D}
    {ef : Option (D × Act)} (h : spendVia look base via units short = .ok ef) :
    (via = none ∧ ef = none) ∨
      ∃ g gc, via = some g ∧ readKind look g kindGrant = .ok gc ∧ spendAt base g gc units (short g) = .ok ef := by
  cases via with
  | none =>
      left
      simp only [spendVia, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨rfl, h.symm⟩
  | some g =>
      right
      simp only [spendVia, except_bind_ok] at h
      obtain ⟨gc, hg, hs⟩ := h
      exact ⟨g, gc, rfl, hg, hs⟩

omit [Ord D] in
/-- Every step a derived transfer passed, and the Draft it is. -/
theorem transfer_ok {X : Ctx D} {look : Pinned D} {a : At D} {srcR dstR : AcctRef D}
    {amount : Nat} {via : Option D} {once : Option ByteArray} {d : Draft D}
    (h : transfer X look a srcR dstR amount via once = .ok d) :
    ∃ scell sv dcell dv principal spend,
      readRef X look srcR = .ok (srcR.resolve X, scell, sv) ∧ readRef X look dstR = .ok (dstR.resolve X, dcell, dv) ∧
      ownerAuthority X look a.actor (srcR.resolve X) scell (.transfer 0) via = .ok principal ∧
      srcR.resolve X ≠ dstR.resolve X ∧ 0 < amount ∧ dv.denom = sv.denom ∧
      Value.fits (sv.balance - amount) = true ∧ Value.fits (dv.balance + amount) = true ∧
      spendVia look transferBase via amount .transferSpent = .ok spend ∧
      d = ⟨[], [(srcR.resolve X, setBalance (sv.balance - amount)), (dstR.resolve X, setBalance (dv.balance + amount))] ++
        spend.toList, (once.map (onceNullifier X (srcR.resolve X))).toList, []⟩ := by
  unfold transfer at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨src, scell, sv⟩, hs, ⟨dst, dcell, dv⟩, hd, principal, ha, ⟨⟩, hne, ⟨⟩, hpos, ⟨⟩, hden, ⟨⟩, hfs, ⟨⟩, hfd,
    spend, hsp, h⟩ := h
  have hs' := hs
  have hd' := hd
  obtain ⟨rfl, -, -⟩ := readRef_ok hs'
  obtain ⟨rfl, -, -⟩ := readRef_ok hd'
  rw [req_ok, decide_eq_true_eq] at hne hpos hden
  rw [req_ok] at hfs hfd
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨scell, sv, dcell, dv, principal, spend, hs, hd, ha, hne, hpos, hden, hfs, hfd, hsp, h.symm⟩

omit [Ord D] in
/-- **Transfer authority** (the twin of `write_authorized`; KERNEL-60). A derived transfer moves
value out of an account only for its owner: the actor (the signer, or the calling object for an
effect), or an actor holding a grant chain for `transfer` on the source whose root issuer is the
owner, and then the grant it holds SPENDS the amount: its transfer ledger had at least `amount`
left, at an index the ledger still reads, and the Turn appends what is left after it. The source is
the account the reference resolves to. -/
theorem transfer_authorized {X : Ctx D} {look : Pinned D} {a : At D} {srcR dstR : AcctRef D}
    {amount : Nat} {via : Option D} {once : Option ByteArray} {d : Draft D}
    (h : transfer X look a srcR dstR amount via once = .ok d) :
    ∃ cell owner, readKind look (srcR.resolve X) kindAccount = .ok cell ∧
      slotDigest X (srcR.resolve X) cell slotOwner = .ok owner ∧
      (via = none ∧ a.actor = owner ∨
        ∃ g, via = some g ∧ Chain X look (srcR.resolve X) (.transfer 0) true g a.actor owner ∧
          ∃ gc i left, readKind look g kindGrant = .ok gc ∧ ledgerLeft transferBase g gc = .ok (i, left) ∧
            amount ≤ left ∧ i ≤ ledgerSpendsMax ∧
            (g, Act.write [.set (transferBase + i) (countBytes (left - amount))]) ∈ d.effects) := by
  obtain ⟨scell, sv, dcell, dv, principal, spend, hs, -, ha, -, hpos, -, -, -, hsp, rfl⟩ := transfer_ok h
  obtain ⟨-, hs, -⟩ := readRef_ok hs
  obtain ⟨hk, -⟩ := readAccount_ok hs
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, -⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨scell, p, hk, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g =>
      right
      rcases spendVia_ok hsp with ⟨h0, -⟩ | ⟨g', gc, hg', hgc, hsa⟩
      · cases h0
      · cases hg'
        obtain ⟨i, left, hl, hu, hc⟩ := spendAt_ok hsa
        rcases hc with ⟨h0, -⟩ | ⟨-, hi, rfl⟩
        · omega
        · exact ⟨g, rfl, walk_chain hp, gc, i, left, hgc, hl, hu, hi, by simp⟩

omit [Ord D] in
/-- **An object pays only from what it owns** (KERNEL-28 (b) with `effect_as_signed`). A transfer an
object's run asks for moves value out of an account only if the OBJECT owns it, or holds a grant
chain for `transfer` on it rooted at its owner whose grant spends the amount (KERNEL-60); the
signer's own authority is not lent. -/
theorem effect_transfer_authorized {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {n : Nat} {wk : Walk D}
    {obj : D} {srcR dstR : AcctRef D} {amount : Nat} {via : Option D} {once : Option ByteArray}
    {r : Draft D × Walk D} (h : tree X look rv c n wk obj (.transfer srcR dstR amount via once) = .ok r) :
    ∃ cell owner, readKind look (srcR.resolve X) kindAccount = .ok cell ∧
      slotDigest X (srcR.resolve X) cell slotOwner = .ok owner ∧
      (via = none ∧ obj = owner ∨
        ∃ g, via = some g ∧ Chain X look (srcR.resolve X) (.transfer 0) true g obj owner ∧
          ∃ gc i left, readKind look g kindGrant = .ok gc ∧ ledgerLeft transferBase g gc = .ok (i, left) ∧
            amount ≤ left ∧ i ≤ ledgerSpendsMax ∧
            (g, Act.write [.set (transferBase + i) (countBytes (left - amount))]) ∈ r.1.effects) := by
  obtain ⟨_, _, _, hd⟩ := effect_as_signed h
  simp only [dispatch] at hd
  exact transfer_authorized (a := ⟨obj, wk.born⟩) (stepped_draft hd)

omit [Ord D] in
/-- Every step a derived credit line passed, and the Draft it is. -/
theorem credit_ok {X : Ctx D} {look : Pinned D} {a : At D} {well : D} {acctR : AcctRef D}
    {amount : Nat} {via : Option D} {d : Draft D} (h : credit X look a well acctR amount via = .ok d) :
    ∃ wcell wv acell av principal spend,
      readAccount look well = .ok (wcell, wv) ∧ readRef X look acctR = .ok (acctR.resolve X, acell, av) ∧
      ownerAuthority X look a.actor well wcell (.credit 0) via = .ok principal ∧
      wv.denom = X.env.bytes well ∧ well ≠ acctR.resolve X ∧ 0 < amount ∧ av.denom = wv.denom ∧
      amount ≤ wv.floor ∧ av.floor + amount ≤ capMax ∧
      spendVia look creditBase via amount .creditSpent = .ok spend ∧
      d = ⟨[], [(well, setFloor (wv.floor - amount)), (acctR.resolve X, setFloor (av.floor + amount))] ++ spend.toList,
        [], []⟩ := by
  unfold credit at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨wcell, wv⟩, hs, ⟨acct, acell, av⟩, hda, principal, ha, ⟨⟩, hwell, ⟨⟩, hne, ⟨⟩, hpos, ⟨⟩, hden, ⟨⟩, hle,
    ⟨⟩, hcap, spend, hsp, h⟩ := h
  have hda' := hda
  obtain ⟨rfl, -, -⟩ := readRef_ok hda'
  rw [req_ok, decide_eq_true_eq] at hwell hne hpos hden hle hcap
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨wcell, wv, acell, av, principal, spend, hs, hda, ha, hwell, hne, hpos, hden, hle, hcap, hsp, h.symm⟩

omit [Ord D] in
/-- **Credit authority** (KERNEL-60). A derived credit line moves floor only out of a WELL (an
account whose denomination is its own id), only with the authority of the well's owner slot (the
signer, or a grant chain for `credit` rooted at that owner whose grant SPENDS the amount from its
credit ledger; `issue` sets the owner to the issuer and no receiver writes an account's owner
slot), and only into a live account of the same denomination. -/
theorem credit_authorized {X : Ctx D} {look : Pinned D} {a : At D} {well : D} {acctR : AcctRef D}
    {amount : Nat} {via : Option D} {d : Draft D} (h : credit X look a well acctR amount via = .ok d) :
    ∃ cell v owner, readKind look well kindAccount = .ok cell ∧ Value.ofCell cell = some v ∧
      v.denom = X.env.bytes well ∧ slotDigest X well cell slotOwner = .ok owner ∧
      (via = none ∧ a.actor = owner ∨
        ∃ g, via = some g ∧ Chain X look well (.credit 0) true g a.actor owner ∧
          ∃ gc i left, readKind look g kindGrant = .ok gc ∧ ledgerLeft creditBase g gc = .ok (i, left) ∧
            amount ≤ left ∧ i ≤ ledgerSpendsMax ∧
            (g, Act.write [.set (creditBase + i) (countBytes (left - amount))]) ∈ d.effects) ∧
      ∃ acell av, readKind look (acctR.resolve X) kindAccount = .ok acell ∧ Value.ofCell acell = some av ∧
        av.denom = v.denom := by
  obtain ⟨wcell, wv, acell, av, principal, spend, hs, hda, ha, hwell, -, hpos, hden, -, -, hsp, rfl⟩ := credit_ok h
  obtain ⟨-, hda, -⟩ := readRef_ok hda
  obtain ⟨hk, hv⟩ := readAccount_ok hs
  obtain ⟨hka, hva⟩ := readAccount_ok hda
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, -⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨wcell, wv, p, hk, hv, hwell, ho, ?_, acell, av, hka, hva, hden⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g =>
      right
      rcases spendVia_ok hsp with ⟨h0, -⟩ | ⟨g', gc, hg', hgc, hsa⟩
      · cases h0
      · cases hg'
        obtain ⟨i, left, hl, hu, hc⟩ := spendAt_ok hsa
        rcases hc with ⟨h0, -⟩ | ⟨-, hi, rfl⟩
        · omega
        · exact ⟨g, rfl, walk_chain hp, gc, i, left, hgc, hl, hu, hi, by simp⟩

omit [Ord D] in
/-- **A transfer's once key is spent.** A derived transfer carries exactly the nullifier of its
once key (if it has one) in its source's namespace, so (`admit_nullifiers`) a transfer with the
same key from the same source lands at most once in the life of the World. Without a key, replay
protection is the transaction id's journal alone. -/
theorem transfer_once {X : Ctx D} {look : Pinned D} {a : At D} {srcR dstR : AcctRef D}
    {amount : Nat} {via : Option D} {once : Option ByteArray} {d : Draft D}
    (h : transfer X look a srcR dstR amount via once = .ok d) :
    d.nullifiers = (once.map (onceNullifier X (srcR.resolve X))).toList := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, rfl⟩ := transfer_ok h
  rfl

/-! ## Births -/

omit [Ord D] [DecidableEq D] in
theorem ofCell_not_value {cell : Cell} (h : cell.discipline ≠ .value) : Value.ofCell cell = none := by
  unfold Value.ofCell; simp [h]

/-- Every value cell a Draft bears is empty: balance 0, floor 0. -/
def ZeroBorn (d : Draft D) : Prop :=
  ∀ p ∈ d.creates, ∀ v, Value.ofCell p.2 = some v → v.balance = 0 ∧ v.floor = 0

omit [Ord D] in
/-- **An object's calls bear only empty value cells**: no callable receiver issues (`issue` is not
callable), `account` bears balance and floor 0, `install` a ROM package cell (KERNEL-75), and the
rest bear no value cell. -/
theorem tree_zeroBorn {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} :
    ∀ n wk a b r, tree X look rv c n wk a b = .ok r → ZeroBorn r.1 := by
  refine tree_all ?_ ?_ ?_
  · intro a b ha hb p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ha p hp
    · exact hb p hp
  · intro _ _ _ _ p hp; simp at hp
  · intro sub wk actor b r hc hi h
    cases b with
    | invoke => simp [Body.isInvoke] at hi
    | account asset owner =>
        have hd := stepped_draft h
        simp only [account, pure, Except.pure, Except.ok.injEq] at hd
        rw [← hd]
        intro p hp v hv
        simp only [List.mem_singleton] at hp
        rw [hp] at hv
        obtain ⟨_, hb, hf⟩ := accountCell_value hv
        exact ⟨hb, by rw [hf]⟩
    | grant target grantee rights parent =>
        have hd := stepped_draft h
        simp only [grant, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        intro p hp v hv
        have := mem_bornAt_cell hp
        simp only [List.mem_singleton] at this
        rw [this, ofCell_not_value (by simp)] at hv
        cases hv
    | transfer src dst amount via once =>
        have hd := stepped_draft h
        obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hr⟩ := transfer_ok hd
        rw [hr]; simp [ZeroBorn]
    | credit well acct amount via =>
        have hd := stepped_draft h
        obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hr⟩ := credit_ok hd
        rw [hr]; simp [ZeroBorn]
    | install pkg =>
        have hd := stepped_draft h
        simp only [install, bind, Except.bind] at hd
        split at hd
        · cases hd
        · simp only [pure, Except.pure, Except.ok.injEq] at hd
          rw [← hd]
          intro p hp v hv
          have := mem_bornAt_cell hp
          simp only [List.mem_singleton] at this
          rw [this, ofCell_not_value (by simp)] at hv
          cases hv
    | _ => simp [Body.callable] at hc

omit [Ord D] in
theorem map_fst_ok {α β ε : Type} {x : Except ε (α × β)} {a : α} (h : x.map (·.1) = .ok a) :
    ∃ r, x = .ok r ∧ r.1 = a := by
  cases x with
  | error e => cases h
  | ok r => simp only [Except.map, Except.ok.injEq] at h; exact ⟨r, rfl, h⟩

omit [Ord D] in
/-- **Which value cells a call bears**, anywhere in its tree. Every born value cell has balance 0;
its floor is 0 unless the signed call is `issue cap`, and then the floor IS the signed cap and the
denomination is the bytes of the turn's first born id: the well names itself. With
`Kernel.Proofs.Value.admit_birth` and `fold_floors_held`, the cap is the denomination's floor sum
forever. -/
theorem derive_value_born {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {d : Draft D}
    (h : derive X look rv c = .ok d) :
    ∀ p ∈ d.creates, ∀ v, Value.ofCell p.2 = some v →
      v.balance = 0 ∧ (v.floor = 0 ∨ ∃ cap, c.unsigned.body = .issue cap ∧ v.floor = cap ∧
        v.denom = X.env.bytes (cellIdOf X.env (txIdOf X c) 0)) := by
  have zero : ZeroBorn d → ∀ p ∈ d.creates, ∀ v, Value.ofCell p.2 = some v →
      v.balance = 0 ∧ (v.floor = 0 ∨ ∃ cap, c.unsigned.body = .issue cap ∧ v.floor = cap ∧
        v.denom = X.env.bytes (cellIdOf X.env (txIdOf X c) 0)) := by
    intro hz p hp v hv
    obtain ⟨hb, hf⟩ := hz p hp v hv
    exact ⟨hb, .inl hf⟩
  rw [derive_eq] at h
  obtain ⟨r, hr, rfl⟩ := map_fst_ok h
  generalize hb : c.unsigned.body = b at hr
  cases b with
  | invoke obj method args budget via =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd⟩ := invoke_ok hr
      have hz : ZeroBorn r.1 := by
        refine foldCalls_all (P := ZeroBorn) ?_ (fun wk a b r h => tree_zeroBorn _ wk a b r h) _ _ ?_ hd
        · intro a b ha hb p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact ha p hp
          · exact hb p hp
        · intro p hp; simp at hp
      have := zero hz
      rwa [hb] at this
  | issue cap =>
      have hd := stepped_draft hr
      simp only [issue, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨⟨⟩, hcap, hd⟩ := hd
      rw [req_ok, decide_eq_true_eq] at hcap
      rw [← hd]
      intro x hx v hv
      have := mem_bornAt_cell hx
      simp only [List.mem_singleton] at this
      rw [this] at hv
      obtain ⟨hden, hbal, hf⟩ := accountCell_value hv
      refine ⟨hbal, .inr ⟨cap, rfl, ?_, hden⟩⟩
      rw [hf]; exact Nat.mod_eq_of_lt (by unfold capMax at hcap; omega)
  | account asset owner =>
      have hd := stepped_draft hr
      simp only [account, pure, Except.pure, Except.ok.injEq] at hd
      rw [← hd]
      intro p hp v hv
      simp only [List.mem_singleton] at hp
      rw [hp] at hv
      obtain ⟨_, hbal, hf⟩ := accountCell_value hv
      exact ⟨hbal, .inl (by rw [hf])⟩
  | enroll key next possession via =>
      have hd := stepped_draft hr
      simp only [enroll, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨_, _, _, _, _, _, ⟨⟩, _, hd⟩ := hd
      rw [← hd]
      intro p hp v hv
      have := mem_bornAt_cell hp
      simp only [List.mem_singleton] at this
      rw [this, ofCell_not_value (by simp)] at hv; cases hv
  | install pkg =>
      have hd := stepped_draft hr
      simp only [install, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨⟨⟩, _, hd⟩ := hd
      rw [← hd]
      intro p hp v hv
      have := mem_bornAt_cell hp
      simp only [List.mem_singleton] at this
      rw [this, ofCell_not_value (by simp)] at hv; cases hv
  | create pkg laws state =>
      have hd := stepped_draft hr
      simp only [create, except_bind_ok, pure, Except.pure] at hd
      obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, hd⟩ := hd
      have hc : r.1.creates = bornAt X c 0 [objectCell X c.unsigned.member pkg laws state] := by
        cases pkg <;>
        · simp only [except_bind_ok, Except.ok.injEq] at hd
          obtain ⟨_, _, hd⟩ := hd
          rw [← hd]
      rw [hc]
      intro p hp v hv
      have := mem_bornAt_cell hp
      simp only [List.mem_singleton] at this
      rw [this, ofCell_not_value (by simp [objectCell])] at hv; cases hv
  | grant target grantee rights parent =>
      have hd := stepped_draft hr
      simp only [grant, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨_, _, ⟨⟩, _, _, _, hd⟩ := hd
      rw [← hd]
      intro p hp v hv
      have := mem_bornAt_cell hp
      simp only [List.mem_singleton] at this
      rw [this, ofCell_not_value (by simp)] at hv; cases hv
  | rotate key next =>
      have hd := stepped_draft hr
      simp only [rotate, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨_, _, ⟨⟩, _, _, _, ⟨⟩, _, hd⟩ := hd
      rw [← hd]; simp
  | write obj edits via =>
      have hd := stepped_draft hr
      simp only [write, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, hd⟩ := hd
      rw [← hd]; simp
  | law obj laws via =>
      have hd := stepped_draft hr
      simp only [law, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, ⟨⟩, _, hd⟩ := hd
      rw [← hd]; simp
  | revoke g =>
      have hd := stepped_draft hr
      simp only [revoke, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
      obtain ⟨_, _, _, _, ⟨⟩, _, hd⟩ := hd
      rw [← hd]; simp
  | transfer src dst amount via once =>
      have hd := stepped_draft hr
      obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hd⟩ := transfer_ok hd
      rw [hd]; simp
  | credit well acct amount via =>
      have hd := stepped_draft hr
      obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hd⟩ := credit_ok hd
      rw [hd]; simp

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

/-- Setting a value cell's floor slot to a `u64` leaves its denomination and balance. -/
theorem ofCell_setFloor {cell : Cell} {v : Value} {f : Nat} (hv : Value.ofCell cell = some v)
    (hf : f < 2 ^ 64) :
    Value.ofCell { cell with slots := applyOps cell.slots [.set Value.floorKey (Value.floorBytes f)] } =
      some { v with floor := f } := by
  have hd := ofCell_value hv
  unfold Value.ofCell at hv ⊢
  simp only [applyOps, List.foldl, applyOp, hd, if_true] at hv ⊢
  rw [slots_get_set_ne _ (by decide : Value.denomKey ≠ Value.floorKey),
    slots_get_set_ne _ (by decide : Value.balanceKey ≠ Value.floorKey), slots_get_set_eq]
  simp only [Option.bind_some, floorOf_bytes, Nat.mod_eq_of_lt hf]
  split at hv
  · rename_i dd bb ff h1 h2 h3
    rw [h1, h2]
    split at hv
    · simp only [Option.some.injEq] at hv; subst hv; simp_all
    · simp at hv
  · simp at hv

theorem pinned_live {E : Env D} {w : World D} {pins : List (D × D)} {c : D} {cell : Cell}
    (h : pinned E w pins c = .ok (some cell)) : w.live E c = some cell := by
  unfold pinned at h; split at h
  · simpa using h
  · simp at h

section Exact
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [Ord D] in
/-- No effect names `k`: the Turn's act at `k` is `keep`. -/
theorem actFor_of_none {efs : List (D × Act)} {k : D} (h : ∀ e ∈ efs, e.1 ≠ k) : actFor efs k = .keep := by
  unfold actFor
  rw [List.find?_eq_none.mpr (fun e he => by simpa using h e he)]

/-- **Sealed writes, forward** (any number of distinct cells; KERNEL-60's transfer writes three). An
admitted turn sealed with effects `efs` leaves at each effect cell whose act is a write what
`postWrite` makes of the cell observed there, and every cell no effect names (and not born) as it
was. -/
theorem sealed_writes {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {efs : List (D × Act)}
    {ns : List D} (hseal : sealTurn X c [] efs ns = .ok t) (ha : World.admit X.env w t = .ok w') :
    (∀ k ops, (∃ e ∈ efs, e.1 = k) → actFor efs k = .write ops →
      ∃ cell post, w.live X.env k = some cell ∧ postWrite k cell ops = .ok post ∧ w'.live X.env k = some post) ∧
      ∀ k, (∀ e ∈ efs, e.1 ≠ k) → k ∉ createdIds t → w'.entry X.env k = w.entry X.env k := by
  obtain ⟨_, _, htouch, _, _, _, _, _, _, hpin⟩ := sealTurn_ok hseal
  refine ⟨fun k ops ⟨e, he, hek⟩ hk => ?_, fun k hk hc => ?_⟩
  · obtain ⟨p, hp, hpk⟩ := hpin e he
    have hx : ({ cell := p.1, seen := p.2, act := actFor efs p.1 } : Touch D) ∈ t.touches := by
      rw [htouch]; exact List.mem_map_of_mem hp
    rw [hpk, hek] at hx
    exact admit_written ha hx (by simp only; rw [hk])
  · refine admit_frame ha (fun x hx hxk => ?_) hc
    rw [htouch] at hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    simp only at hxk ⊢
    rw [hxk]
    exact actFor_of_none hk

/-- **Two sealed writes, forward.** An admitted turn sealed with writes on two distinct cells
leaves at each what `postWrite` makes of the cell observed there, and every other cell (not born)
as it was (`sealed_writes` at two). -/
theorem sealed_two_writes {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {a b : D}
    {opsA opsB : List Op} {ns : List D}
    (hseal : sealTurn X c [] [(a, .write opsA), (b, .write opsB)] ns = .ok t) (hab : a ≠ b)
    (ha : World.admit X.env w t = .ok w') :
    (∃ ca pa, w.live X.env a = some ca ∧ postWrite a ca opsA = .ok pa ∧ w'.live X.env a = some pa) ∧
      (∃ cb pb, w.live X.env b = some cb ∧ postWrite b cb opsB = .ok pb ∧ w'.live X.env b = some pb) ∧
      ∀ k, k ≠ a → k ≠ b → k ∉ createdIds t → w'.entry X.env k = w.entry X.env k := by
  obtain ⟨hw, hfr⟩ := sealed_writes hseal ha
  refine ⟨hw a opsA ⟨_, List.mem_cons_self, rfl⟩ (by simp [actFor]),
    hw b opsB ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩ (by simp [actFor, hab]),
    fun k h1 h2 hc => hfr k ?_ hc⟩
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact Ne.symm h1
  · exact Ne.symm h2

omit [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- The grant a use of a counted right spends is a grant, so it is neither account the use moves
value between (a pinned id has one cell, of one kind). -/
theorem grant_ne_account {look : Pinned D} {g k : D} {gc kc : Cell}
    (hg : readKind look g kindGrant = .ok gc) (hk : readKind look k kindAccount = .ok kc) : g ≠ k := by
  rintro rfl
  obtain ⟨h1, h2⟩ := readKind_ok hg
  obtain ⟨h3, h4⟩ := readKind_ok hk
  rw [h1] at h3
  cases h3
  rw [h2] at h4
  exact absurd h4 (by decide)

/-- **An admitted transfer moves exactly `amount`**, and nothing else: the source's balance falls
by it, the destination's rises by it, both keep their denomination and floor; through a grant
(`via = some g`, KERNEL-60), the grant's transfer ledger had at least `amount` left and now holds
what is left after it, appended at its next index; and every other cell is untouched (L1's
`transfer_conserves`, on touches). -/
theorem transfer_exact {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {srcR dstR : AcctRef D}
    {amount : Nat} {via : Option D} {once : Option ByteArray}
    (hb : c.unsigned.body = .transfer srcR dstR amount via once)
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') :
    ∃ sv dv, (w.live X.env (srcR.resolve X)).bind Value.ofCell = some sv ∧
      (w.live X.env (dstR.resolve X)).bind Value.ofCell = some dv ∧
      (w'.live X.env (srcR.resolve X)).bind Value.ofCell = some { sv with balance := sv.balance - amount } ∧
      (w'.live X.env (dstR.resolve X)).bind Value.ofCell = some { dv with balance := dv.balance + amount } ∧
      (∀ g, via = some g → ∃ gc i left post, w.live X.env g = some gc ∧
        ledgerLeft transferBase g gc = .ok (i, left) ∧ amount ≤ left ∧
        postWrite g gc [.set (transferBase + i) (countBytes (left - amount))] = .ok post ∧
        w'.live X.env g = some post) ∧
      ∀ k, k ≠ srcR.resolve X → k ≠ dstR.resolve X → via ≠ some k → k ∉ createdIds t →
        w'.entry X.env k = w.entry X.env k := by
  obtain ⟨_, d, hdd, hsl⟩ := receiveWith_sealed (receive_ok_with hr).2
  rw [derive_eq, hb] at hdd
  simp only [dispatch, stepped_map] at hdd
  obtain ⟨scell, sv, dcell, dv, principal, spend, hs, hd, -, hne, hpos, -, hfs, hfd, hsp, rfl⟩ := transfer_ok hdd
  obtain ⟨-, hs, -⟩ := readRef_ok hs
  obtain ⟨-, hd, -⟩ := readRef_ok hd
  obtain ⟨hks, hvs⟩ := readAccount_ok hs
  obtain ⟨hkd, hvd⟩ := readAccount_ok hd
  have hls := pinned_live (readKind_ok hks).1
  have hld := pinned_live (readKind_ok hkd).1
  obtain ⟨hw, hfr⟩ := sealed_writes hsl ha
  obtain ⟨c1, p1, hc1, hw1, hl1⟩ := hw (srcR.resolve X) [.set Value.balanceKey (Value.balanceBytes (sv.balance - amount))]
    ⟨(srcR.resolve X, setBalance (sv.balance - amount)), by simp, rfl⟩ (by simp [actFor, setBalance])
  obtain ⟨c2, p2, hc2, hw2, hl2⟩ := hw (dstR.resolve X) [.set Value.balanceKey (Value.balanceBytes (dv.balance + amount))]
    ⟨(dstR.resolve X, setBalance (dv.balance + amount)), by simp, rfl⟩ (by simp [actFor, setBalance, hne])
  rw [hls] at hc1; cases hc1
  rw [hld] at hc2; cases hc2
  refine ⟨sv, dv, by rw [hls]; exact hvs, by rw [hld]; exact hvd, ?_, ?_, ?_, ?_⟩
  · rw [hl1, postWrite_eq hw1]; exact ofCell_setBalance hvs hfs
  · rw [hl2, postWrite_eq hw2]; exact ofCell_setBalance hvd hfd
  · intro g hg
    subst hg
    rcases spendVia_ok hsp with ⟨h0, -⟩ | ⟨g', gc, hg', hgc, hsa⟩
    · cases h0
    · cases hg'
      obtain ⟨i, left, hl, hu, hc⟩ := spendAt_ok hsa
      rcases hc with ⟨h0, -⟩ | ⟨-, -, rfl⟩
      · omega
      · have n1 := grant_ne_account hgc hks
        have n2 := grant_ne_account hgc hkd
        obtain ⟨c3, p3, hc3, hw3, hl3⟩ := hw g [.set (transferBase + i) (countBytes (left - amount))]
          ⟨(g, .write [.set (transferBase + i) (countBytes (left - amount))]), by simp, rfl⟩ (by simp [actFor, setBalance, Ne.symm n1, Ne.symm n2])
        have hlg := pinned_live (readKind_ok hgc).1
        rw [hlg] at hc3; cases hc3
        exact ⟨gc, i, left, p3, hlg, hl, hu, hw3, hl3⟩
  · intro k h1 h2 h3 hc
    refine hfr k ?_ hc
    intro e he
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with (rfl | rfl) | he
    · exact Ne.symm h1
    · exact Ne.symm h2
    · rcases spendVia_ok hsp with ⟨-, rfl⟩ | ⟨g', gc, rfl, -, hsa⟩
      · simp at he
      · obtain ⟨i, left, -, -, hc'⟩ := spendAt_ok hsa
        rcases hc' with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
        · simp at he
        · simp only [Option.toList_some, List.mem_singleton] at he
          subst he
          exact fun e => h3 (congrArg some e)

/-- **An admitted credit line moves exactly `amount` of floor** out of the well into the account
(`0 < amount ≤` the well's floor, so the well's `-` does not truncate): balances and
denominations unchanged; through a grant (`via = some g`, KERNEL-60), the grant's credit ledger had
at least `amount` left and now holds what is left after it; every other cell untouched (the
`createdIds` exclusion is empty: a credit bears nothing). That no credit line raises what may be
outstanding is a separate, kernel result: `fold_floors_held` and `outstanding_le_cap`. -/
theorem credit_exact {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {well : D}
    {acctR : AcctRef D} {amount : Nat} {via : Option D}
    (hb : c.unsigned.body = .credit well acctR amount via)
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') :
    ∃ wv av, (w.live X.env well).bind Value.ofCell = some wv ∧
      (w.live X.env (acctR.resolve X)).bind Value.ofCell = some av ∧
      wv.denom = X.env.bytes well ∧ av.denom = wv.denom ∧ 0 < amount ∧ amount ≤ wv.floor ∧
      (w'.live X.env well).bind Value.ofCell = some { wv with floor := wv.floor - amount } ∧
      (w'.live X.env (acctR.resolve X)).bind Value.ofCell = some { av with floor := av.floor + amount } ∧
      (∀ g, via = some g → ∃ gc i left post, w.live X.env g = some gc ∧
        ledgerLeft creditBase g gc = .ok (i, left) ∧ amount ≤ left ∧
        postWrite g gc [.set (creditBase + i) (countBytes (left - amount))] = .ok post ∧
        w'.live X.env g = some post) ∧
      ∀ k, k ≠ well → k ≠ acctR.resolve X → via ≠ some k → k ∉ createdIds t →
        w'.entry X.env k = w.entry X.env k := by
  obtain ⟨_, d, hdd, hsl⟩ := receiveWith_sealed (receive_ok_with hr).2
  rw [derive_eq, hb] at hdd
  simp only [dispatch, stepped_map] at hdd
  obtain ⟨wcell, wv, acell, av, principal, spend, hs, hda, -, hwell, hne, hpos, hden, hle, hcap, hsp, rfl⟩ :=
    credit_ok hdd
  obtain ⟨-, hda, -⟩ := readRef_ok hda
  obtain ⟨hks, hvs⟩ := readAccount_ok hs
  obtain ⟨hkd, hvd⟩ := readAccount_ok hda
  have hls := pinned_live (readKind_ok hks).1
  have hld := pinned_live (readKind_ok hkd).1
  obtain ⟨hw, hfr⟩ := sealed_writes hsl ha
  obtain ⟨c1, p1, hc1, hw1, hl1⟩ := hw well [.set Value.floorKey (Value.floorBytes (wv.floor - amount))]
    ⟨(well, setFloor (wv.floor - amount)), by simp, rfl⟩ (by simp [actFor, setFloor])
  obtain ⟨c2, p2, hc2, hw2, hl2⟩ := hw (acctR.resolve X) [.set Value.floorKey (Value.floorBytes (av.floor + amount))]
    ⟨(acctR.resolve X, setFloor (av.floor + amount)), by simp, rfl⟩ (by simp [actFor, setFloor, hne])
  rw [hls] at hc1; cases hc1
  rw [hld] at hc2; cases hc2
  refine ⟨wv, av, by rw [hls]; exact hvs, by rw [hld]; exact hvd, hwell, hden, hpos, hle, ?_, ?_, ?_, ?_⟩
  · rw [hl1, postWrite_eq hw1]
    exact ofCell_setFloor hvs (by have := ofCell_floor_lt hvs; omega)
  · rw [hl2, postWrite_eq hw2]
    exact ofCell_setFloor hvd (by unfold capMax at hcap; omega)
  · intro g hg
    subst hg
    rcases spendVia_ok hsp with ⟨h0, -⟩ | ⟨g', gc, hg', hgc, hsa⟩
    · cases h0
    · cases hg'
      obtain ⟨i, left, hl, hu, hc⟩ := spendAt_ok hsa
      rcases hc with ⟨h0, -⟩ | ⟨-, -, rfl⟩
      · omega
      · have n1 := grant_ne_account hgc hks
        have n2 := grant_ne_account hgc hkd
        obtain ⟨c3, p3, hc3, hw3, hl3⟩ := hw g [.set (creditBase + i) (countBytes (left - amount))]
          ⟨(g, .write [.set (creditBase + i) (countBytes (left - amount))]), by simp, rfl⟩ (by simp [actFor, setFloor, Ne.symm n1, Ne.symm n2])
        have hlg := pinned_live (readKind_ok hgc).1
        rw [hlg] at hc3; cases hc3
        exact ⟨gc, i, left, p3, hlg, hl, hu, hw3, hl3⟩
  · intro k h1 h2 h3 hc
    refine hfr k ?_ hc
    intro e he
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with (rfl | rfl) | he
    · exact Ne.symm h1
    · exact Ne.symm h2
    · rcases spendVia_ok hsp with ⟨-, rfl⟩ | ⟨g', gc, rfl, -, hsa⟩
      · simp at he
      · obtain ⟨i, left, -, -, hc'⟩ := spendAt_ok hsa
        rcases hc' with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
        · simp at he
        · simp only [Option.toList_some, List.mem_singleton] at he
          subst he
          exact fun e => h3 (congrArg some e)

end Exact

end Nanodregg.Kernel.Receive
