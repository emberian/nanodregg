/-
# Protocol.Proofs.Behind — a call refused stale BEHIND is never admitted later (PROTOCOL-57)

The settlement's `refused staleCode` arm (KERNEL-54, PROTOCOL-52) is final BY THEOREM: the member's
own call, as `plan` signed it at a World `w₀` of follow's fold, that follow's World `w` reached from
`w₀` refuses `stale`, is admitted by no `submit` at any World the fold reaches from `w`, or the
deployed hash collides among the call's pin inputs at `w₀` and there (`behindPres`, an explicit
list). The pieces: `plan_pins` (the W0 premise: every pin `plan` signs is the planning World's, and
the ranges it signs are the command's), `signedReads_ranges` (each such range is pinned at the planning
World's listing), `receive_pins` (a derived Turn checks every pin its call carries, at any World),
`Kernel.admit_stale_pin` (a `stale` refusal names a pin that disagrees), and
`Kernel.stale_behind_forever` / `row_stale_behind_forever` / `range_stale_behind_forever` (a pin
stale on the fold stays stale), with `Kernel.headOf_width_fold` (a relation's key width is the one
it was declared with, along the fold).
-/
import Protocol.Proofs.Command
import Kernel.Proofs.StaleOnly
import Kernel.Proofs.Versions

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive
open Nanodregg.Codec.Kernel (Cell.Fits)

variable {D : Type} [Ord D] [DecidableEq D]

/-- Every cell pin `derivePins` adds is the planning World's own `pinOf`. -/
theorem derivePins_pins {X : Ctx D} {w : World D} :
    ∀ (n : Nat) (u u' : Unsigned D) (t : Turn D), derivePins X w n u = .ok (u', t) →
      ∀ p ∈ u'.pins, p ∈ u.pins ∨ p.2 = Kernel.pinOf X.env (w.entry X.env p.1)
  | 0, _, _, _, h => by simp [derivePins] at h
  | n + 1, u, u', t, h => by
      simp only [derivePins] at h
      split at h
      · intro p hp
        rcases derivePins_pins n _ u' t h p hp with hm | hk
        · simp only [List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact .inl hm
          · exact .inr rfl
        · exact .inr hk
      · split at h
        · cases h
        · have := derivePins_pins n _ u' t h
          simpa using this
      · cases h
      · cases h; intro p hp; exact .inl hp

/-- `derivePins` never adds a range read. -/
theorem derivePins_ranges {X : Ctx D} {w : World D} :
    ∀ (n : Nat) (u u' : Unsigned D) (t : Turn D), derivePins X w n u = .ok (u', t) → u'.ranges = u.ranges
  | 0, _, _, _, h => by simp [derivePins] at h
  | n + 1, u, u', t, h => by
      simp only [derivePins] at h
      split at h
      · have := derivePins_ranges n _ u' t h
        simpa using this
      · split at h
        · cases h
        · have := derivePins_ranges n _ u' t h
          simpa using this
      · cases h
      · cases h; rfl

/-- **The pins `plan` signs are the planning World's** (KERNEL-54, the W0 premise of the BEHIND
finality): every cell pin is `pinOf` of `w`'s entry, every row pin is `rowPinAt` of `w`, and the
call's range reads are exactly the ones it was handed (`signedReads`, whose pins `signedReads_ranges`
states). -/
theorem plan_pins {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray} {rs : SignedReads D}
    {b : Body D} {u : Unsigned D} (h : plan X me w key rs b = .ok u) :
    (∀ p ∈ u.pins, p.2 = Kernel.pinOf X.env (w.entry X.env p.1)) ∧
      (∀ p ∈ u.rowPins, ∃ k, p = rowPinAt X.env w k) ∧ u.ranges = rs.ranges := by
  unfold plan at h
  split at h
  · cases h
  · rename_i u' t hp
    split at h
    · cases h
    · cases h
      refine ⟨?_, planUnchecked_rowPins hp, ?_⟩
      · simp only [planUnchecked, bind, Except.bind] at hp
        split at hp
        · cases hp
        · rename_i q hq
          obtain ⟨u1, t1⟩ := q
          simp only at hp
          split at hp
          · cases hp
          · cases hp
            intro p hm
            rcases derivePins_pins _ _ _ _ hq p hm with hm | hk
            · simp at hm
            · exact hk
      · simp only [planUnchecked, bind, Except.bind] at hp
        split at hp
        · cases hp
        · rename_i q hq
          obtain ⟨u1, t1⟩ := q
          simp only at hp
          split at hp
          · cases hp
          · cases hp
            exact derivePins_ranges _ _ _ _ hq

omit [Ord D] in
/-- `Kernel.rangeOf` listing rows is the relation's head at that width and `rangeRows` there. -/
theorem rangeOf_some {E : Env D} {r : Rows D} {parent : D} {rel : Nat} {pre : ByteArray} {most width : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : rangeOf E r parent rel pre most = some (width, some l)) :
    ∃ c s lim cap rt, headOf E r parent rel = some (c, s, lim, cap, width, rt) ∧
      rangeRows E r parent rel width pre most = some l := by
  unfold rangeOf at h
  cases hh : headOf E r parent rel with
  | none => simp [hh] at h
  | some v =>
    obtain ⟨c, s, lim, cap, width', rt⟩ := v
    simp only [hh, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    exact ⟨c, s, lim, cap, rt, rfl, h2⟩

/-- The range `invokeRange` signs is pinned at the planning World's listing: its parent is live at
`w`, its prefix is no wider than the relation's keys, and its `seen` is THE pin admission recomputes
(`Kernel.rangePin` at the relation's width and floor over `rangeRows` at `w`). -/
theorem invokeRange_pins {X : Ctx D} {w : World D} {o : D} {rel : String} {most : Nat}
    {pre : Option String} {q : RangeRead D} (h : invokeRange X w o rel most pre = .ok q) :
    (∃ cell, w.live X.env q.parent = some cell) ∧ ∃ c s lim cap width rt l,
      headOf X.env w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧ q.pre.size ≤ width ∧
      rangeRows X.env w.rows q.parent q.rel width q.pre q.most = some l ∧
      q.seen = rangePin X.env q.parent q.rel width q.pre (headFloor X.env w.rows q.parent q.rel) l := by
  unfold invokeRange at h
  cases hl : w.live X.env o with
  | none => rw [hl] at h; cases h
  | some cell =>
    rw [hl] at h
    simp only at h
    cases hr : relationOf X w o cell rel with
    | error r => rw [hr] at h; cases h
    | ok p =>
      obtain ⟨i, d⟩ := p
      rw [hr] at h
      simp only at h
      by_cases hlim : most ≤ d.limit
      · rw [if_pos hlim] at h
        cases hL : rangeListing X w o i d most pre with
        | error r => rw [hL] at h; cases h
        | ok v =>
          obtain ⟨pb, width, l⟩ := v
          rw [hL] at h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨-, hro, hw⟩ := rangeListing_ok hL
          obtain ⟨c, s, lim, cap, rt, hh, hrr⟩ := rangeOf_some hro
          exact ⟨⟨cell, hl⟩, c, s, lim, cap, width, rt, l, hh, hw, hrr, rfl⟩
      · rw [if_neg hlim] at h; cases h

/-- **Every range `signedReads` lists is pinned at the planning World's listing** (item 4, the W0
premise's range half): `invokeRange_pins` for each, so the signer's range pin is `w`'s own. -/
theorem signedReads_ranges {X : Ctx D} {w : World D} {cmd : Cmd D} {rs : SignedReads D}
    (h : signedReads X w cmd = .ok rs) :
    ∀ q ∈ rs.ranges, (∃ cell, w.live X.env q.parent = some cell) ∧ ∃ c s lim cap width rt l,
      headOf X.env w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧ q.pre.size ≤ width ∧
      rangeRows X.env w.rows q.parent q.rel width q.pre q.most = some l ∧
      q.seen = rangePin X.env q.parent q.rel width q.pre (headFloor X.env w.rows q.parent q.rel) l := by
  unfold signedReads at h
  split at h
  · rename_i o _ _ rd _
    intro q hq
    cases hp : rd.points.mapM (invokePoint X w o) with
    | error e =>
      cases hr : rd.range with
      | none => simp [hr, hp, bind, Except.bind, pure, Except.pure] at h
      | some x =>
        obtain ⟨rel, most, pre⟩ := x
        cases hq' : invokeRange X w o rel most pre <;>
          simp [hr, hp, hq', bind, Except.bind, pure, Except.pure] at h
    | ok ps =>
      cases hr : rd.range with
      | none =>
        simp only [hr, hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h; cases hq
      | some x =>
        obtain ⟨rel, most, pre⟩ := x
        cases hq' : invokeRange X w o rel most pre with
        | error e => simp [hr, hq', bind, Except.bind] at h
        | ok q' =>
          simp only [hr, hp, hq', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [List.mem_singleton] at hq
          subst hq
          exact invokeRange_pins hq'
  · cases h
    intro q hq
    cases hq

/-- A range read's pin inputs at a World whose relation lists `l` at the head's width. -/
theorem rangePresAt_of {E : Env D} {w : World D} {q : RangeRead D} {c s lim cap width : Nat} {rt : Bool}
    {l : List (RowSlot D × RowLeaf)} (hh : headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt))
    (hl : rangeRows E w.rows q.parent q.rel width q.pre q.most = some l) :
    rangePresAt E w q = rangePre E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l :: leafPres l := by
  simp [rangePresAt, hh, hl]

/-- Every row pin of a call is a row touch of its Turn, at the digest the caller saw. -/
theorem rowTouchesOf_pins {pins : List (RowSlot D × D)} {rows : List (RowSlot D × RowAct)}
    {rts : List (RowTouch D)} (h : rowTouchesOf pins rows = .ok rts) :
    (∀ p ∈ pins, ∃ x ∈ rts, x.slot = p.1 ∧ x.seen = some p.2) ∧
      ∀ x ∈ rts, ∀ s, x.seen = some s → (x.slot, s) ∈ pins := by
  unfold rowTouchesOf at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, h⟩ := h
  split at h
  · simp [bind, Except.bind] at h
  · simp only [except_bind_ok] at h
    obtain ⟨⟨⟩, -, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨fun p hp => ⟨_, List.mem_append_left _ (List.mem_map_of_mem hp), rfl, rfl⟩, ?_⟩
    intro x hx s hs
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      cases hs
      exact hp
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      cases hs

/-- **A derived Turn checks every pin its call carries** (the receive half of the BEHIND
finality): its touches are the call's cell pins, every row pin is a row touch at the caller's
digest, and its range reads are the call's. Whatever World derived it. -/
theorem receive_pins {X : Ctx D} {v : World D} {c : Call D} {t : Turn D} (h : receive X v c = .ok t) :
    t.touches.map (fun x => (x.cell, x.seen)) = c.unsigned.pins ∧
      (∀ p ∈ c.unsigned.rowPins, ∃ x ∈ t.rows, x.slot = p.1 ∧ x.seen = some p.2) ∧
      (∀ x ∈ t.rows, ∀ s, x.seen = some s → (x.slot, s) ∈ c.unsigned.rowPins) ∧
      t.ranges = c.unsigned.ranges := by
  refine ⟨(receive_derived h).pinned, ?_⟩
  obtain ⟨-, d, -, hs⟩ := receiveWith_sealed (receive_ok_with h).2
  unfold sealTurn at hs
  simp only [except_bind_ok] at hs
  obtain ⟨⟨⟩, -, rts, hr, hs⟩ := hs
  split at hs
  · simp only [Except.ok.injEq] at hs
    subst hs
    exact ⟨(rowTouchesOf_pins hr).1, (rowTouchesOf_pins hr).2, rfl⟩
  · cases hs

/-- **What `checkPins` refuses is a disagreement** (the contrapositive of `checkPins_ok_iff`): a cell
pin not its cell's entry's pin, a row pin not its row's, or a range read not its listing's. -/
theorem checkPins_error_disagree {E : Env D} {w : World D} {pins : List (D × D)}
    {rowPins : List (RowSlot D × D)} {ranges : List (RangeRead D)}
    (h : checkPins E w pins rowPins ranges ≠ .ok ()) :
    (∃ p ∈ pins, Kernel.pinOf E (w.entry E p.1) ≠ p.2) ∨
    (∃ p ∈ rowPins, ∃ key, p.1 = .row key ∧
        rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠ p.2) ∨
    (∃ q ∈ ranges, ∃ c s lim cap width rt l,
        headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧
        rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
        rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l ≠ q.seen) := by
  refine Classical.byContradiction fun hn => h (checkPins_ok_iff.mpr ⟨?_, ?_, ?_⟩)
  · intro p hp; exact Classical.byContradiction fun hne => hn (.inl ⟨p, hp, hne⟩)
  · intro p hp key hk
    exact Classical.byContradiction fun hne => hn (.inr (.inl ⟨p, hp, key, hk, hne⟩))
  · intro q hq c s lim cap width rt l hh hl
    exact Classical.byContradiction fun hne =>
      hn (.inr (.inr ⟨q, hq, c, s, lim, cap, width, rt, l, hh, hl, hne⟩))

/-- **A call refused stale BEHIND on follow's fold is never admitted later** (cv 01a15187; the
settlement's `refused staleCode` arm, PROTOCOL-52's "final by fold structure" now by theorem). The
member's own call, as `plan` signed it at a World `w₀` of follow's fold (the W0 premise: its pins
are `w₀`'s, `plan_pins`, and its range reads are `signedReads`' at `w₀`, `signedReads_ranges`), that follow's World `w` reached from `w₀` refuses `stale`
(`staleBehind`), is admitted by no `submit` at any World `w'` the fold reaches from `w`, unless the
deployed hash collides among the call's pin inputs at `w₀` and `w'` (`behindPres`). -/
theorem staleBehind_final [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {n : Nat}
    (hE : X.env.Lawful n) {me : Self D} {w₀ w w' : World D} {l₁ l₂ : List (Kernel.Step D)}
    {key : ByteArray} {cmd : Cmd D} {rs : SignedReads D} {b : Body D} {u : Unsigned D} {c : Call D}
    (hf : w₀.CellsFit Cell.Fits X.env) (hr : w₀.RowsCanon X.env) (hok : w₀.RowsOk X.env)
    (hrs : signedReads X w₀ cmd = .ok rs) (hplan : plan X me w₀ key rs b = .ok u) (hc : c.unsigned = u)
    (h₁ : World.fold X.env w₀ l₁ = .ok w) (h₂ : World.fold X.env w l₂ = .ok w')
    (hs : staleBehind X me w c = true) :
    (∀ r, submit X w' c ≠ .ok r) ∨ CollidesAmong X.env.hash (behindPres X.env w₀ w' u) := by
  obtain ⟨-, -, -, -, y, hcp⟩ := staleBehind_spec hs
  obtain ⟨hpc, hpr, hpq⟩ := plan_pins hplan
  have hrw := fold_rowsCanon hr h₁
  have hrw' := fold_rowsCanon hrw h₂
  by_cases hsub : ∃ r, submit X w' c = .ok r
  case neg => exact .inl fun r hr => hsub ⟨r, hr⟩
  obtain ⟨⟨t', v⟩, hsub⟩ := hsub
  right
  obtain ⟨-, hrt', hat'⟩ := submit_ok hsub
  obtain ⟨htc', htr', -, htq'⟩ := receive_pins hrt'
  have hne0 : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges ≠ .ok () := by
    rw [hcp]; exact fun h => by cases h
  rcases checkPins_error_disagree hne0 with
      ⟨⟨xc, xs⟩, hm, hne⟩ | ⟨⟨xslot, s⟩, hm, k, hxs, hne⟩ | ⟨q, hq, c₁, s₁, lim₁, cap₁, width₁, rt₁, l₁, hh₁, hl₁, hne₁⟩
  · -- a cell pin
    simp only at hne
    have hseen : xs = Kernel.pinOf X.env (w₀.entry X.env xc) := by
      have hm0 := hm; rw [hc] at hm0; exact hpc _ hm0
    have hm' : (xc, xs) ∈ t'.touches.map (fun x => (x.cell, x.seen)) := by rw [htc']; exact hm
    obtain ⟨x', hx', he⟩ := List.mem_map.mp hm'
    simp only [Prod.mk.injEq] at he
    have hp' := admit_pins hat' x' hx'
    rw [he.1, he.2, hseen] at hp'
    rcases stale_behind_forever hf h₁ h₂ (c := xc) (by rw [← hseen]; exact hne) with h | h
    · exact (h hp').elim
    · refine CollidesAmong.mono ?_ h
      intro z hz
      refine List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨_, by rw [← hc]; exact hm, ?_⟩))
      simpa using hz
  · -- a row pin
    simp only at hxs hne
    subst hxs
    rw [hc] at hm
    obtain ⟨k', hk'⟩ := hpr _ hm
    simp only [rowPinAt, Prod.mk.injEq, RowSlot.row.injEq] at hk'
    obtain ⟨rfl, rfl⟩ := hk'
    obtain ⟨x', hx', hs', hseen'⟩ := htr' _ (by rw [hc]; exact hm)
    simp only at hs' hseen'
    have hp' := admit_row_pins hrw' hat' x' hx' k _ hs' hseen'
    rcases row_stale_behind_forever hE hr hok h₁ h₂ (key := k) hne with h | h | h
    · exact (h hp').elim
    · have hl : w'.live X.env k.parent = none := by simp [World.live, h]
      exact (admit_dead hl ⟨x', hx', hs'⟩ hat').elim
    · refine CollidesAmong.mono ?_ h
      intro z hz
      refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hm, ?_⟩))
      simpa using hz
  · -- a range pin: `plan` signed it at `w₀`'s listing (`signedReads_ranges`)
    have hq0 : q ∈ rs.ranges := by rw [hc, hpq] at hq; exact hq
    have hqu : q ∈ u.ranges := by rw [hpq]; exact hq0
    have hq' : q ∈ t'.ranges := by rw [htq', hc]; exact hqu
    obtain ⟨⟨cell₀, hlive₀⟩, c₀, s₀, lim₀, cap₀, width₀, rt₀, l₀, hh₀, hwd, hl₀, hseen₀⟩ :=
      signedReads_ranges hrs q hq0
    obtain ⟨c₂, s₂, lim₂, cap₂, width₂, rt₂, l', hh₂, hl', hpin'⟩ := admit_range_pins hat' q hq'
    -- a relation's key width is its declaration's, along the fold
    have hw₁ : width₁ = width₀ := headOf_width_fold hr h₁ hh₀ hh₁
    have hw₂ : width₂ = width₀ :=
      (headOf_width_fold hrw h₂ hh₁ hh₂).trans hw₁
    subst hw₁ hw₂
    rcases range_stale_behind_forever hE hr hok h₁ h₂ hwd hl₀ hl₁ hl' (by rw [← hseen₀]; exact hne₁)
      with h | h | h
    · exact (h (hpin'.trans hseen₀)).elim
    · -- the parent tombed at `w'`: admission checked its cell pin (the parent is touched), which
      -- `plan` signed at `w₀`, where it was live: the tomb's pin input and the live one collide
      obtain ⟨_, hk, _⟩ := admit_ok hat'
      have hq'' := (forEx_ok.mp hk.ranges) q hq'
      simp only [except_bind_ok] at hq''
      obtain ⟨⟨⟩, hreq, -⟩ := hq''
      obtain ⟨x, hx, hxc⟩ := List.any_eq_true.mp (req_ok.mp hreq)
      have hxc : x.cell = q.parent := of_decide_eq_true hxc
      have hm' : (x.cell, x.seen) ∈ c.unsigned.pins := by rw [← htc']; exact List.mem_map_of_mem hx
      have hseen : x.seen = Kernel.pinOf X.env (w₀.entry X.env x.cell) := by
        rw [hc] at hm'; exact hpc _ hm'
      have hp' := admit_pins hat' x hx
      rw [hseen, hxc, h] at hp'
      obtain ⟨v, he₀⟩ : ∃ v, w₀.entry X.env q.parent = some (.live cell₀ v) := by
        cases he : w₀.entry X.env q.parent with
        | none => simp [World.live, he] at hlive₀
        | some e =>
          cases e with
          | tomb => simp [World.live, he] at hlive₀
          | live c' v =>
            simp only [World.live, he, Option.some.injEq] at hlive₀
            exact ⟨v, by rw [hlive₀]⟩
      rw [he₀, pinOf_eq_pre, pinOf_eq_pre] at hp'
      have hne : pinPre X.env (some Entry.tomb) ≠ pinPre X.env (some (.live cell₀ v)) := fun he =>
        absurd (congrArg Prod.fst he) (show domTomb ≠ domCell by unfold domTomb domCell; decide)
      refine CollidesAmong.mono ?_ (CollidesAmong.pair hne hp')
      intro z hz
      refine List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨_, by rw [← hc]; exact hm', ?_⟩))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [hxc, he₀, h, List.mem_cons, List.not_mem_nil, or_false]
      rcases hz with rfl | rfl
      · exact .inr rfl
      · exact .inl rfl
    · refine CollidesAmong.mono ?_ h
      intro z hz
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hqu, ?_⟩)
      rw [rangePresAt_of hh₀ hl₀, rangePresAt_of hh₂ hl']
      simp only [List.mem_cons, List.mem_append] at hz ⊢
      rcases hz with hz | hz | hz | hz
      · exact .inl (.inl hz)
      · exact .inr (.inl hz)
      · exact .inl (.inr hz)
      · exact .inr (.inr hz)

/-- TOOTH (`staleBehind_final`): where the hash separates the call's pin inputs at the two Worlds,
a call refused stale BEHIND is admitted by no later World of the fold. -/
theorem staleBehind_final_sep [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {n : Nat}
    (hE : X.env.Lawful n) {me : Self D} {w₀ w w' : World D} {l₁ l₂ : List (Kernel.Step D)}
    {key : ByteArray} {cmd : Cmd D} {rs : SignedReads D} {b : Body D} {u : Unsigned D} {c : Call D}
    (hf : w₀.CellsFit Cell.Fits X.env) (hr : w₀.RowsCanon X.env) (hok : w₀.RowsOk X.env)
    (hrs : signedReads X w₀ cmd = .ok rs) (hplan : plan X me w₀ key rs b = .ok u) (hc : c.unsigned = u)
    (h₁ : World.fold X.env w₀ l₁ = .ok w) (h₂ : World.fold X.env w l₂ = .ok w')
    (hsep : Separates X.env.hash (behindPres X.env w₀ w' u))
    (hs : staleBehind X me w c = true) : ∀ r, submit X w' c ≠ .ok r :=
  hsep.elim (staleBehind_final hE hf hr hok hrs hplan hc h₁ h₂ hs)

end Nanodregg.Protocol.Command
