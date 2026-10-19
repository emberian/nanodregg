/-
# Host.Proofs.Coherence — every index entry points at its own record (cv 01a15180-9499)

`index.log` and the loop's entries since the base hold one entry per record: the step count and
chain BEFORE the record and the offset of its frame (`Host.indexed` at open, the same push in
`Host.append`). A page locates ONE entry and walks the segment from it (`Page.build`), so what a
page serves rests on every entry pointing at its own record. HOST-60 read that off the code; here
it is a theorem.

The coherence:
* `Page.Indexes` — over the entries in index order and the tip (the durable end of the segment,
  the World's step count): entry i's offset holds a frame that verifies against the 32 bytes
  before it (`Page.frameOf`, what a page reads) and decodes to steps, and the next entry (the tip,
  after the last) sits at that frame's end, at the step count those steps leave.
  `Page.Indexes.not_dup` is its tooth: one entry twice in a row is not coherent.
* `StoreIndexes` — the Store's: the entries the base counts read back at their positions under
  the Store's index key and are a coherent run to the base (`Deployed.Coherent` at the deployed
  instance).

What a page gets from it:
* `Page.build_nonempty` — **HOST-60's lift**: over a coherent index, every page `build` serves
  from a `start` short of the tip holds at least one event. `Page.build_empty_incoherent` is the
  tooth: one entry pointing at the durable end serves an EMPTY page short of the tip.
* `Page.build_beforeLog_first` — **HOST-61's entry-0 case**: a page is refused `beforeLog` only
  from a `start` below the step count of the entry its search reads first (entry 0). This one
  needs no coherence (`locate` moves only to entries at or below `start`); with
  `build_nonempty`, a page from `start` in [entry 0's step count, the tip) is served non-empty or
  refused by another name.
* `Deployed.page_nonempty` (at the deployed open and the deployed pager, over a coherent Store)
  and `Deployed.page_beforeLog_first` (the deployed pager over any Store).

Both page theorems are about a page `build` returns: neither says a page over a coherent Store is
served rather than refused (`badIndex`, `corrupt`).

Every Store written at an open is coherent (the completeness side):
* `openWith_indexes` — the open's entries since the base continue the base's run to the open's
  position and World (`indexed_indexes`: each entry `Host.indexed` makes is the frame the open
  verified);
* `StoreIndexes.of_open_empty` — a Store with an empty `index.log` (genesis, import, a follower's
  adopted base): `Deployed.genesis_indexes`, `Deployed.import_indexes`;
* `StoreIndexes.append` — records and entries (or orphans) appended;
* `StoreIndexes.cut_open` — the writer's truncation at open;
* `sealed_indexes` — a seal: the old base's entries, then the open's (`Deployed.sealed_indexes_deployed`);
* `Page.Indexes.snoc` — the pure core of the loop's append (one record's frame and its entry).

Not proved:
* that the loop between two opens holds the entries `Indexes.snoc` describes. `append` pushes
  `⟨steps, pos.offset, chain⟩` after the frame's sync (Host/Loop.lean), which is read off the code.
  Every open re-derives the loop's entries (`openWith_indexes`). But a seal the loop makes after
  appends (`makeRoom`'s and the cadence's `sealNow`, a member checkpoint) counts the loop's own
  entries, so a Store last sealed there is coherent only through that unproved push;
* that an entry's chain is the chain before its record: `Indexes` pins the offset and the step
  count, not `e.chain` (from which a page states its chain). A wrong chain field is caught by the
  follower's chain check, not here;
* that entry 0 is the Store's first record (see `Deployed.page_beforeLog_first`).
-/
import Host.Proofs.Page
import Host.Proofs.Seal

namespace Nanodregg.Host.Page

open Nanodregg.Kernel Nanodregg.Codec

/-- **Index-segment coherence**: the entries `L`, in index order, against `tip` (the durable end
of the segment, the World's step count). Entry i's offset holds a frame that verifies against the
32 bytes before it (`frameOf`, what a page reads) and decodes to steps `ts`; the next entry, or
the tip after the last, sits at that frame's end and at the step count `ts` leaves. -/
def Indexes {D : Type} (dc : Codec.Stream D) (s : Log.Sealer) (recordMax : Nat)
    (read : Nat → Nat → Id ByteArray) : List Entry → Nat × Nat → Prop
  | [], _ => True
  | e :: rest, tip => ∃ (r : ByteArray) (ts : List (Kernel.Step D × D)),
      frameOf s recordMax read e.offset = some r ∧ (Record.codec dc).decode r = .ok ts ∧
      (match rest with | [] => tip | e' :: _ => (e'.offset, e'.steps)) =
        (e.offset + frameSize r, e.steps + ts.length) ∧
      Indexes dc s recordMax read rest tip

variable {D : Type}

theorem frameSize_pos (r : ByteArray) : 0 < frameSize r := by
  unfold frameSize; omega

/-- Every entry of a coherent index begins before the durable end. -/
theorem Indexes.offset_lt {dc : Codec.Stream D} {s : Log.Sealer} {recordMax : Nat}
    {read : Nat → Nat → Id ByteArray} {tip : Nat × Nat} :
    ∀ (rest : List Entry) (e : Entry), Indexes dc s recordMax read (e :: rest) tip → e.offset < tip.1
  | [], e, h => by
    obtain ⟨r, ts, -, -, hn, -⟩ := h
    simp only at hn
    rw [hn]; exact Nat.lt_add_of_pos_right (frameSize_pos r)
  | e' :: rest, e, h => by
    obtain ⟨r, ts, -, -, hn, hr⟩ := h
    simp only [Prod.mk.injEq] at hn
    have := Indexes.offset_lt rest e' hr
    have := frameSize_pos r
    omega

/-- **The tooth of `Indexes`**: an index holding one entry twice in a row (two entries at one
record) is not coherent: the next entry must sit at its record's frame end, past it. -/
theorem Indexes.not_dup {dc : Codec.Stream D} {s : Log.Sealer} {recordMax : Nat}
    {read : Nat → Nat → Id ByteArray} {tip : Nat × Nat} (e : Entry) (rest : List Entry) :
    ¬ Indexes dc s recordMax read (e :: e :: rest) tip := by
  rintro ⟨r, ts, -, -, hn, -⟩
  simp only [Prod.mk.injEq] at hn
  have := frameSize_pos r
  omega

/-- A suffix of a coherent index is coherent. -/
theorem Indexes.drop {dc : Codec.Stream D} {s : Log.Sealer} {recordMax : Nat}
    {read : Nat → Nat → Id ByteArray} {tip : Nat × Nat} :
    ∀ (k : Nat) (L : List Entry), Indexes dc s recordMax read L tip → Indexes dc s recordMax read (L.drop k) tip
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | k + 1, _ :: rest, h => by
    obtain ⟨_, _, _, _, _, hr⟩ := h
    exact Indexes.drop k rest hr

/-- A record whose every step is at or below `start` is skipped whole: the page keeps its
events, bytes and `full`, and its count moves past the record. -/
theorem foldl_walkStep_skip (E : Kernel.Env D) (budget start : Nat) :
    ∀ (ts : List (Kernel.Step D × D)) (a : Acc) (c : D) (k : Nat), a.full = false → a.steps = k →
      k + ts.length ≤ start →
      (ts.foldl (walkStep E budget start) (a, c, k)).1.events = a.events ∧
      (ts.foldl (walkStep E budget start) (a, c, k)).1.bytes = a.bytes ∧
      (ts.foldl (walkStep E budget start) (a, c, k)).1.full = false ∧
      (ts.foldl (walkStep E budget start) (a, c, k)).1.steps = k + ts.length
  | [], a, _, k, hf, hk, _ => by simpa using ⟨hf, hk⟩
  | (t, root) :: ts, a, c, k, hf, _, hle => by
    rw [List.foldl_cons]
    have hs1 : k + 1 ≤ start := by simp only [List.length_cons] at hle; omega
    have hw : walkStep E budget start (a, c, k) (t, root) =
        ({ a with steps := k + 1, chain := E.bytes (Kernel.stepLink E c t root) },
          Kernel.stepLink E c t root, k + 1) := by
      simp only [walkStep, hf, Bool.false_eq_true, ↓reduceIte, if_pos hs1]
    rw [hw]
    have := foldl_walkStep_skip E budget start ts
      { a with steps := k + 1, chain := E.bytes (Kernel.stepLink E c t root) }
      (Kernel.stepLink E c t root) (k + 1) hf rfl (by simp only [List.length_cons] at hle; omega)
    simp only [List.length_cons] at this ⊢
    refine ⟨this.1, this.2.1, this.2.2.1, by omega⟩

/-- **A walk over a coherent index serves**: from an empty page at a coherent entry at or below
`start`, with one fuel per entry from it on, a tip past `start` leaves the page holding an event. -/
theorem walk_indexes [Ord D] [DecidableEq D] {dc : Codec.Stream D} {PD : D → Prop} (hd : Codec.Stream.LawfulOn PD dc)
    {E : Kernel.Env D} {s : Log.Sealer} {recordMax budget : Nat} {read : Nat → Nat → Id ByteArray}
    {endOff now start : Nat} (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) (hs : start < now) :
    ∀ (rest : List Entry) (e : Entry) (c : D) (acc a : Acc),
      Indexes dc s recordMax read (e :: rest) (endOff, now) →
      acc.events = #[] → acc.bytes = 0 → acc.full = false → acc.steps = e.steps → e.steps ≤ start →
      walk E dc s recordMax budget read endOff start (rest.length + 1) e.offset c acc = .ok a →
      0 < a.events.size := by
  intro rest
  induction rest with
  | nil =>
    intro e c acc a hI hev hb hf hk hle h
    have hoff := Indexes.offset_lt [] e hI
    obtain ⟨r, ts, hr, hdec, hn, -⟩ := hI
    simp only [Prod.mk.injEq] at hn
    exact walk_serves hd hB hev hb hf hoff hr hdec (by omega) (by omega) h
  | cons e' rest ih =>
    intro e c acc a hI hev hb hf hk hle h
    have hoff := Indexes.offset_lt (e' :: rest) e hI
    obtain ⟨r, ts, hr, hdec, hn, hI'⟩ := hI
    simp only [Prod.mk.injEq] at hn
    by_cases hp : start < acc.steps + ts.length
    · exact walk_serves hd hB hev hb hf hoff hr hdec (by omega) hp h
    · cases ts with
      | nil =>
        exfalso
        simp only [walk, bind, pure, hf, Bool.false_or, decide_eq_true_eq,
          if_neg (Nat.not_le.mpr hoff)] at h
        revert h
        show (match frameOf s recordMax read e.offset with | _ => _) = _ → False
        rw [hr]
        simp only [hdec]
        intro h; cases h
      | cons p ps =>
        have hw : walk E dc s recordMax budget read endOff start ((e' :: rest).length + 1) e.offset c acc =
            walk E dc s recordMax budget read endOff start (rest.length + 1) (e.offset + frameSize r)
              (walkTurnsAt E budget start c acc.steps (p :: ps) acc).2.1
              (walkTurnsAt E budget start c acc.steps (p :: ps) acc).1 := by
          simp only [walk, bind, pure, hf, Bool.false_or, decide_eq_true_eq,
            if_neg (Nat.not_le.mpr hoff)]
          show (match frameOf s recordMax read e.offset with | _ => _) = _
          rw [hr]
          simp only [hdec]
        rw [hw] at h
        obtain ⟨hev', hb', hf', hk'⟩ := foldl_walkStep_skip E budget start (p :: ps) acc c acc.steps hf rfl
          (by omega)
        rw [← hn.1] at h
        exact ih e' _ _ a hI' (by rw [← hev]; exact hev') (by rw [← hb]; exact hb') hf'
          (by rw [hk', hn.2, hk]) (by omega) h

/-- **A page short of the tip is non-empty** (HOST-60's lift, cv 01a15180-9499). Over a coherent
index `L` (`Indexes`, to the durable end and the World's step count) whose reader returns, at each
position it answers, the entry `L` holds there, every page `build` serves from a `start` short of
the tip holds at least one event (with the digest codec lawful and a budget of
`eventBytesMax + 5`, `budget_fits_event` for the deployed one). The tooth is
`build_empty_incoherent`. -/
theorem build_nonempty [Ord D] [DecidableEq D] {dc : Codec.Stream D} {PD : D → Prop} (hd : Codec.Stream.LawfulOn PD dc)
    {E : Kernel.Env D} {digestOf : ByteArray → Option D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {get : Nat → Id (Except Fault Entry)} {endOff : Nat}
    {now : Nat × ByteArray} {start : Nat} {a : Acc} {L : List Entry}
    (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget)
    (hget : ∀ k e, get k = .ok e → L[k]? = some e)
    (hL : Indexes dc s recordMax read L (endOff, now.1)) (hs : start < now.1)
    (h : build E dc digestOf s recordMax budget read get L.length endOff now start = .ok a) :
    0 < a.events.size := by
  rcases build_located h with ⟨hn, -⟩ | ⟨k, e, c, -, hg, hle, -, hw⟩
  · omega
  · have hk := hget k e hg
    have hlt : k < L.length := (List.getElem?_eq_some_iff.mp hk).1
    have hdrop : L.drop k = e :: L.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.mp hk).2]
    have hI := Indexes.drop k L hL
    rw [hdrop] at hI
    have hf : L.length - k = (L.drop (k + 1)).length + 1 := by simp only [List.length_drop]; omega
    rw [hf] at hw
    exact walk_indexes hd hB hs (L.drop (k + 1)) e c _ a hI rfl rfl rfl rfl hle hw

/-- **The tooth of `build_nonempty`**: one entry, at or below `start`, pointing at the durable end
(no frame of the index's own there) serves an EMPTY page short of the tip. -/
theorem build_empty_incoherent (E : Kernel.Env D) (dc : Codec.Stream D) (digestOf : ByteArray → Option D)
    (s : Log.Sealer) (recordMax budget : Nat) (read : Nat → Nat → Id ByteArray) (endOff : Nat)
    (now : Nat × ByteArray) (start : Nat) (e : Entry) (c : D) (hs : start < now.1) (hle : e.steps ≤ start)
    (hc : digestOf e.chain = some c) (hend : endOff ≤ e.offset) :
    build E dc digestOf s recordMax budget read (fun _ => pure (.ok e)) 1 endOff now start =
      .ok { steps := e.steps, chain := e.chain } := by
  simp only [build, locate, locate.go, walk, bind, pure, if_neg (Nat.not_le.mpr hs),
    Nat.one_ne_zero, ↓reduceIte, Nat.le_refl, if_neg (Nat.not_lt.mpr hle), hc,
    Bool.false_or, decide_eq_true_eq, hend]

theorem locate_go_le (get : Nat → Id (Except Fault Entry)) (start : Nat) :
    ∀ (fuel lo hi : Nat) (e : Entry), e.steps ≤ start → ∀ {k : Nat} {e' : Entry},
      locate.go get start fuel lo hi e = .ok (k, e') → e'.steps ≤ start := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi e he k e' hg
    simp only [locate.go, pure] at hg
    cases hg; exact he
  | succ fuel ih =>
    intro lo hi e he k e' hg
    simp only [locate.go] at hg
    split at hg
    · simp only [pure] at hg; cases hg; exact he
    · simp only [bind] at hg
      split at hg
      · simp only [pure] at hg; cases hg
      · rename_i em _
        split at hg
        · rename_i hm; exact ih _ hi em hm hg
        · exact ih lo _ e he hg

theorem walk_error {E : Kernel.Env D} {dc : Codec.Stream D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {endOff start : Nat} :
    ∀ (fuel off : Nat) (c : D) (acc : Acc) (f : Fault),
      walk E dc s recordMax budget read endOff start fuel off c acc = .error f → ∃ o, f = .corrupt o := by
  intro fuel
  induction fuel with
  | zero => intro off c acc f h; simp only [walk, pure] at h; cases h
  | succ fuel ih =>
    intro off c acc f h
    simp only [walk, bind, pure] at h
    split at h
    · cases h
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · split at h
        · cases h; exact ⟨_, rfl⟩
        · cases h; exact ⟨_, rfl⟩
        · exact ih _ _ _ _ h

theorem locate_go_error (get : Nat → Id (Except Fault Entry)) (start : Nat) :
    ∀ (fuel lo hi : Nat) (e : Entry) {f : Fault}, locate.go get start fuel lo hi e = .error f →
      ∃ k, get k = .error f := by
  intro fuel
  induction fuel with
  | zero => intro lo hi e f hg; simp only [locate.go, pure] at hg; cases hg
  | succ fuel ih =>
    intro lo hi e f hg
    simp only [locate.go] at hg
    split at hg
    · simp only [pure] at hg; cases hg
    · simp only [bind] at hg
      split at hg
      · rename_i f' hm
        simp only [pure] at hg; cases hg; exact ⟨_, hm⟩
      · split at hg
        · exact ih _ _ _ hg
        · exact ih _ _ _ hg

/-- A search refused was refused by one of its reads. -/
theorem locate_error {get : Nat → Id (Except Fault Entry)} {count start : Nat} {f : Fault}
    (h : locate get count start = .error f) : ∃ k, get k = .error f := by
  simp only [locate, bind] at h
  split at h
  · rename_i f' hg
    simp only [pure] at h; cases h; exact ⟨0, hg⟩
  · exact locate_go_error get start _ _ _ _ h

/-- A search whose first read is at or below `start` returns an entry at or below `start`. -/
theorem locate_le {get : Nat → Id (Except Fault Entry)} {count start k : Nat} {e : Entry}
    (h : locate get count start = .ok (k, e)) (h0 : ∀ e₀, get 0 = .ok e₀ → e₀.steps ≤ start) :
    e.steps ≤ start := by
  simp only [locate, bind] at h
  split at h
  · simp only [pure] at h; cases h
  · rename_i e₀ hg
    exact locate_go_le get start _ _ _ e₀ (h0 e₀ hg) h

/-- `entryAt` refuses only `badIndex`, at the position it was asked for. -/
theorem entryAt_error {keys : Keys} {rd : Nat → Nat → ByteArray} {disk : Nat} {mem : Array Entry}
    {k : Nat} {f : Fault} (h : entryAt (m := Id) keys (fun o l => pure (rd o l)) disk mem k = .error f) :
    f = .badIndex k := by
  simp only [entryAt] at h
  split at h
  · simp only [bind, pure] at h
    split at h
    · cases h
    · cases h; rfl
  · split at h
    · simp only [pure] at h; cases h
    · simp only [pure] at h; cases h; rfl

/-- **A page is refused `beforeLog` only from below the entry its search reads first** (HOST-61's
entry-0 case, cv 01a15180-9499): when the index's reader never refuses `beforeLog` itself
(`entryAt` refuses only `badIndex`, `entryAt_error`) and answers entry 0 with `e₀`, a `build` over
a non-empty index refused `beforeLog` had a `start` below `e₀`'s step count. So from any `start` at
or past entry 0's step count a page is served or refused by another name, and when it is served
short of the tip it is non-empty over a coherent index (`build_nonempty`). This needs no coherence:
`locate` moves only to entries at or below `start`. -/
theorem build_beforeLog_first [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {digestOf : ByteArray → Option D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {get : Nat → Id (Except Fault Entry)} {count endOff : Nat}
    {now : Nat × ByteArray} {start x y : Nat} {e₀ : Entry} (hc : count ≠ 0) (h0 : get 0 = .ok e₀)
    (hgetb : ∀ k x y, get k ≠ .error (.beforeLog x y))
    (h : build E dc digestOf s recordMax budget read get count endOff now start = .error (.beforeLog x y)) :
    start < e₀.steps := by
  refine Nat.lt_of_not_le fun hle => ?_
  have h0le : ∀ e, get 0 = .ok e → e.steps ≤ start := fun e hg => by
    rw [h0] at hg; cases hg; exact hle
  by_cases hn : now.1 ≤ start
  · simp [build, hn] at h
  rcases hl : locate get count start with f | ⟨k, e⟩
  · simp [build, hn, hc, hl] at h
    simp only [bind, pure] at h
    cases h
    obtain ⟨k, hk⟩ := locate_error hl
    exact hgetb k x y hk
  · have hle' := locate_le hl h0le
    have hnl : ¬ start < e.steps := by omega
    cases hd : digestOf e.chain with
    | none =>
      simp [build, hn, hc, hl] at h
      simp only [bind, hnl, hd, ↓reduceIte] at h
      cases h
    | some c =>
      simp [build, hn, hc, hl] at h
      simp only [bind, hnl, hd, ↓reduceIte] at h
      obtain ⟨o, ho⟩ := walk_error _ _ _ _ _ h
      cases ho

end Nanodregg.Host.Page

namespace Nanodregg.Host

open Nanodregg.Host.Log ByteArray
open Nanodregg.Host.Page (Indexes frameOf)

/-! ## The frames a page reads, over bytes -/

theorem frameAt_next {s : Sealer} {rm : Nat} {log prev : ByteArray} {rd : Read} {len : Nat}
    (h : frameAt s rm log 0 prev = some rd) (hl : lenAt log 0 = some len) :
    rd.next = 4 + len + tagBytes := by
  unfold frameAt at h
  rw [hl] at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; simp
      · cases h

theorem frameSize_ge (r : ByteArray) : 4 + tagBytes ≤ frameSize r := by
  unfold frameSize; omega

/-- **A page's frame read depends only on the bytes before the frame's end**: a frame `frameOf`
reads at `off` over `S` is read the same over any `S'` agreeing with `S` below `N`, when the frame
ends at or before `N`. -/
theorem frameOf_congr {s : Sealer} {rm N off : Nat} {S S' r : ByteArray}
    (hS : ∀ i j, j ≤ N → S.extract i j = S'.extract i j)
    (h : frameOf s rm (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) off = some r)
    (hN : off + frameSize r ≤ N) :
    frameOf s rm (fun o l => (pure (S'.extract o (o + l)) : Id ByteArray)) off = some r := by
  have hf := frameSize_ge r
  unfold frameOf at h ⊢
  simp only [bind, pure] at h ⊢
  rw [← hS (off - tagBytes) (off - tagBytes + tagBytes) (by unfold tagBytes at hf ⊢; omega),
    ← hS off (off + 4) (by unfold tagBytes at hf; omega)]
  split at h
  · cases h
  · rename_i len hl
    split at h
    · cases h
    · rename_i hlen
      rw [if_neg hlen]
      cases hfa : frameAt s rm (S.extract off (off + (4 + len + tagBytes))) 0
          (S.extract (off - tagBytes) (off - tagBytes + tagBytes)) with
      | none => rw [hfa] at h; cases h
      | some rd =>
        rw [hfa] at h
        simp only [Option.map_some] at h
        cases h
        obtain ⟨h4, hhead⟩ := lenAt_some hl
        have hb4 : 4 ≤ (S.extract off (off + (4 + len + tagBytes))).size := by
          obtain ⟨-, hnx, hx, -⟩ := frameAt_some hfa
          have := congrArg ByteArray.size hx
          rw [size_frame, size_extract] at this
          omega
        have hbl : lenAt (S.extract off (off + (4 + len + tagBytes))) 0 = some len := by
          refine lenAt_of_occurs ⟨by rw [size_lenBytes]; omega, ?_⟩ (lenAt_lt hl)
          rw [size_lenBytes, ← hhead, extract_extract, extract_extract]
          simp only [size_extract] at h4 hb4
          congr 1 <;> omega
        have hn := frameAt_next hfa hbl
        obtain ⟨-, hnx, hx, -⟩ := frameAt_some hfa
        have hsz := congrArg ByteArray.size hx
        rw [size_frame, size_extract] at hsz
        have hfs : frameSize rd.record = 4 + len + tagBytes := by
          unfold frameSize; omega
        rw [← hS off (off + (4 + len + tagBytes)) (by omega), hfa]
        rfl

/-- A frame written at `off`, after the 32 bytes it chains from, is what a page reads there. -/
theorem frameOf_frame {s : Sealer} {rm off : Nat} {S prev r : ByteArray}
    (hp : S.extract (off - tagBytes) (off - tagBytes + tagBytes) = prev)
    (hf : S.extract off (off + frameSize r) = frame s prev r) (hr : r.size ≤ rm) (hr32 : r.size < 2 ^ 32) :
    frameOf s rm (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) off = some r := by
  have sub : ∀ k l, l ≤ frameSize r → S.extract (off + k) (off + l) = (frame s prev r).extract k l := by
    intro k l hl
    rw [← hf, extract_extract]
    congr 1; omega
  obtain ⟨f0, -, -⟩ := frame_fields s prev r ByteArray.empty
  rw [ByteArray.append_empty] at f0
  have hhead : S.extract off (off + 4) = lenBytes r.size := by
    have := sub 0 4 (by unfold frameSize; omega)
    rw [Nat.add_zero] at this
    rw [this, f0]
  have hl : lenAt (lenBytes r.size) 0 = some r.size :=
    lenAt_of_occurs ⟨by simp [size_lenBytes], by rw [size_lenBytes]; exact extract_zero_size⟩ hr32
  have hbuf : S.extract off (off + (4 + r.size + tagBytes)) = frame s prev r := hf
  have hfa := frameAt_frame s (recordMax := rm) ByteArray.empty prev r ByteArray.empty hr hr32
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty] at hfa
  unfold frameOf
  simp only [bind, pure]
  rw [hp, hhead, hl]
  simp only
  rw [if_neg (by omega), hbuf, hfa]
  rfl

/-- Where the entry after `e` begins (or the tip, after the last). -/
theorem Indexes.next_le {D : Type} {dc : Codec.Stream D} {s : Sealer} {rm : Nat}
    {read : Nat → Nat → Id ByteArray} {tip : Nat × Nat} (rest : List Entry)
    (h : Indexes dc s rm read rest tip) :
    (match rest with | [] => tip | e' :: _ => (e'.offset, e'.steps)).1 ≤ tip.1 := by
  cases rest with
  | nil => exact Nat.le_refl _
  | cons e' rest => exact Nat.le_of_lt (Page.Indexes.offset_lt rest e' h)

/-- **Coherence depends only on the bytes before the tip**: a coherent index over `S` is coherent
over any `S'` that agrees with `S` below the tip's offset. -/
theorem Indexes.congr {D : Type} {dc : Codec.Stream D} {s : Sealer} {rm : Nat} {S S' : ByteArray}
    {tip : Nat × Nat} (hS : ∀ i j, j ≤ tip.1 → S.extract i j = S'.extract i j) :
    ∀ L : List Entry, Indexes dc s rm (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L tip →
      Indexes dc s rm (fun o l => (pure (S'.extract o (o + l)) : Id ByteArray)) L tip
  | [], _ => trivial
  | e :: rest, h => by
    obtain ⟨r, ts, hr, hdec, hn, hI⟩ := h
    have hle := Indexes.next_le rest hI
    rw [hn] at hle
    exact ⟨r, ts, frameOf_congr hS hr hle, hdec, hn, Indexes.congr hS rest hI⟩

/-- Two coherent runs, the second beginning where the first ends, are one coherent run. -/
theorem Indexes.append {D : Type} {dc : Codec.Stream D} {s : Sealer} {rm : Nat}
    {read : Nat → Nat → Id ByteArray} {tip : Nat × Nat} :
    ∀ (A B : List Entry) (p : Nat × Nat), Indexes dc s rm read A p → Indexes dc s rm read B tip →
      (match B with | [] => tip | e :: _ => (e.offset, e.steps)) = p →
      Indexes dc s rm read (A ++ B) tip
  | [], _, _, _, hB, _ => hB
  | [a], B, p, hA, hB, hp => by
    obtain ⟨r, ts, hr, hdec, hn, -⟩ := hA
    refine ⟨r, ts, hr, hdec, ?_, hB⟩
    simp only at hn
    rw [← hn, ← hp]
    cases B <;> rfl
  | a :: a' :: A, B, p, hA, hB, hp => by
    obtain ⟨r, ts, hr, hdec, hn, hA'⟩ := hA
    exact ⟨r, ts, hr, hdec, hn, Indexes.append (a' :: A) B p hA' hB hp⟩

theorem extract_split {S A B : ByteArray} {off : Nat} (h : S.extract off (off + (A ++ B).size) = A ++ B) :
    S.extract off (off + A.size) = A ∧ S.extract (off + A.size) (off + A.size + B.size) = B := by
  have e1 : (S.extract off (off + (A ++ B).size)).extract 0 A.size = S.extract off (off + A.size) := by
    rw [extract_extract, Nat.add_zero, size_append, Nat.min_eq_left (by omega)]
  have e2 : (S.extract off (off + (A ++ B).size)).extract A.size (A.size + B.size) =
      S.extract (off + A.size) (off + A.size + B.size) := by
    rw [extract_extract, size_append, ← Nat.add_assoc, Nat.min_self]
  exact ⟨by rw [← e1, h, extract_append_eq_left rfl], by rw [← e2, h, extract_append_eq_right rfl rfl]⟩

/-- **The entries an indexed fold makes point at their records** (`Host.indexed`, the one place an
entry is made): over a segment holding `encodeAll s prev rs` at `off`, after the 32 bytes `prev`
it chains from, the fold's new entries are a coherent run to where it ends (its offset and its
World's step count), beginning at `off` and the starting World's step count, when each fold step
decodes its record to steps that move the step count by their number (`hstep`). -/
theorem indexed_indexes {W F D : Type} {dc : Codec.Stream D} {s : Sealer} {rm : Nat} {S : ByteArray}
    (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W)
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length) :
    ∀ (rs : List ByteArray) (w : W) (idx : Array Entry) (off : Nat) (prev : ByteArray)
      {st : W × Array Entry × Nat},
      (∀ r ∈ rs, r.size ≤ rm ∧ r.size < 2 ^ 32) →
      S.extract (off - tagBytes) (off - tagBytes + tagBytes) = prev →
      S.extract off (off + (encodeAll s prev rs).size) = encodeAll s prev rs →
      rs.foldlM (indexed mark step) (w, idx, off) = .ok st →
      ∃ M, st.2.1.toList = idx.toList ++ M ∧
        Indexes dc s rm (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) M (st.2.2, (mark st.1).1) ∧
        (match M with | [] => (st.2.2, (mark st.1).1) | e :: _ => (e.offset, e.steps)) = (off, (mark w).1)
  | [], w, idx, off, prev, st, _, _, _, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, trivial, rfl⟩
  | r :: rs, w, idx, off, prev, st, hb, hp, he, h => by
    simp only [List.foldlM] at h
    cases hs : step w r with
    | error e => simp [indexed, hs, bind, Except.bind] at h
    | ok w' =>
      rcases hm : mark w with ⟨a, ch⟩
      simp only [indexed, hs, hm, bind, Except.bind, pure, Except.pure] at h
      have hfs : (frame s prev r).size = frameSize r := by rw [size_frame]; rfl
      simp only [encodeAll] at he
      obtain ⟨he1, he2⟩ := extract_split he
      rw [hfs] at he1 he2
      have hp2 : S.extract (off + frameSize r - tagBytes) (off + frameSize r - tagBytes + tagBytes) =
          s.tag (prev ++ r) := by
        obtain ⟨-, -, f2⟩ := frame_fields s prev r ByteArray.empty
        rw [ByteArray.append_empty] at f2
        rw [← f2, ← he1, extract_extract]
        unfold frameSize
        congr 1 <;> omega
      obtain ⟨M, hM, hI, hhd⟩ := indexed_indexes mark step hstep rs w' (idx.push ⟨a, off, ch⟩)
        (off + frameSize r) (s.tag (prev ++ r)) (fun x hx => hb x (by simp [hx])) hp2 he2 h
      obtain ⟨ts, hdec, hmk⟩ := hstep w r w' hs
      refine ⟨⟨a, off, ch⟩ :: M, by rw [hM]; simp, ⟨r, ts, frameOf_frame hp he1 (hb r (by simp)).1
        (hb r (by simp)).2, hdec, ?_, hI⟩, rfl⟩
      rw [hhd, hmk, hm]

/-- **The loop's append keeps the run coherent** (the pure core of `Host.append`, Host/Loop.lean,
which pushes `⟨steps, pos.offset, chain⟩` as `Host.indexed` does): a coherent run over a segment
`S` ending at the tip `(S.size, h)` (past the origin frame), the frame of a record chained from the 32 bytes before the
end appended, and the record decoding to steps `ts`: the run with the record's entry is coherent
to the new end and the step count `ts` leaves. -/
theorem Indexes.snoc {D : Type} {dc : Codec.Stream D} {s : Sealer} {rm : Nat} {S prev r : ByteArray}
    {h : Nat} {ch : ByteArray} {L : List Entry} {ts : List (Kernel.Step D × D)}
    (hL : Indexes dc s rm (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L (S.size, h))
    (h32 : tagBytes ≤ S.size) (hp : S.extract (S.size - tagBytes) (S.size - tagBytes + tagBytes) = prev)
    (hr : r.size ≤ rm) (hr32 : r.size < 2 ^ 32) (hdec : (Record.codec dc).decode r = .ok ts) :
    Indexes dc s rm (fun o l => (pure ((S ++ frame s prev r).extract o (o + l)) : Id ByteArray))
      (L ++ [⟨h, S.size, ch⟩]) (S.size + frameSize r, h + ts.length) := by
  have hfs : (frame s prev r).size = frameSize r := by rw [size_frame]; rfl
  have hL' := Indexes.congr (S' := S ++ frame s prev r)
    (fun i j (hj : j ≤ S.size) => (extract_append_le hj).symm) L hL
  have hf : (S ++ frame s prev r).extract S.size (S.size + frameSize r) = frame s prev r := by
    exact extract_append_eq_right rfl (by rw [hfs])
  have hp' : (S ++ frame s prev r).extract (S.size - tagBytes) (S.size - tagBytes + tagBytes) = prev := by
    rw [extract_append_le (by omega)]; exact hp
  refine Indexes.append L [⟨h, S.size, ch⟩] (S.size, h) ?_ ?_ rfl
  · exact Indexes.congr (fun _ _ _ => rfl) L hL'
  · exact ⟨r, ts, frameOf_frame hp' hf hr hr32, hdec, rfl, trivial⟩

/-! ## The Store: every entry the base counts, and every entry since -/

/-- **The Store's index points at its records** (cv 01a15180-9499): the base file decodes to a
base `b`; the first `b.indexCount` entries of `index.log` (all inside it) read back at their
positions under the Store's index key as `L`; and `L` is a coherent run over the segment to the
base (its offset and its World's step count), the segment reaching the base. What the deployed
open adds to it is the tail's entries (`openWith_indexes`). Every Store this Host writes has it:
`StoreIndexes.of_open_empty` (genesis, import, adopt: no entry), `StoreIndexes.append` (records
and orphans appended), `StoreIndexes.cut_open` (the writer's truncation at open), `sealed_indexes`
(a seal). -/
def StoreIndexes {W D : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (dc : Codec.Stream D) (file I S : ByteArray) :
    Prop :=
  ∃ (b : Base W) (n : Nat) (d : ByteArray) (L : List Entry), Base.read keys c world file = .ok (b, n, d) ∧
    L.length = b.indexCount ∧ L.length * entryBytes keys ≤ I.size ∧ b.offset ≤ S.size ∧
    (∀ (i : Nat) (hi : i < L.length), Entry.read (keys.forStore (origin b.world)) i
      (I.extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys)) = some L[i]) ∧
    Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L
      (b.offset, (mark b.world).1)

variable {W F D : Type}

/-- **The open's entries point at their records**: over a Store whose base's entries are a
coherent run to the base, the one open's entries since the base continue it to the open's
position and World (`Host.indexed` makes each from the frame the open verified), when each fold
step decodes its record to steps that move the step count by their number (`hstep`). -/
theorem openWith_indexes (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o)
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d)) {L : List Entry}
    (hL : Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L
      (b.offset, (mark b.world).1)) :
    Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray))
      (L ++ o.index.toList) (o.pos.offset, (mark o.opened.world).1) := by
  obtain ⟨b', _, _, _, op, _, hb', hlen, hoff, htag, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  obtain ⟨rs, he, hf, _, _, hrs⟩ := open_sound_bounded keys.segment (indexed mark step) _ _ _ hop
  have hesz : (encodeAll keys.segment b.tag.bytes rs).size = op.validLen := by
    rw [← he]; simp only [size_extract]; omega
  have he' : S.extract b.offset (b.offset + (encodeAll keys.segment b.tag.bytes rs).size) =
      encodeAll keys.segment b.tag.bytes rs := by
    rw [hesz, ← he, extract_extract]; congr 1 <;> omega
  have hp : S.extract (b.offset - tagBytes) (b.offset - tagBytes + tagBytes) = b.tag.bytes := by
    rw [show b.offset - tagBytes + tagBytes = b.offset by omega]; exact htag
  obtain ⟨M, hM, hI, hhd⟩ := indexed_indexes (dc := dc) (S := S) mark step hstep rs b.world #[] b.offset
    b.tag.bytes hrs hp he' hf
  have hend := openLog_indexed_off keys.segment c.recordBytesMax mark step b.world #[] b.offset _ _ hop
  simp only [List.nil_append] at hM
  dsimp only
  rw [hM, ← hend]
  exact Indexes.append L M _ hL hI hhd

/-- A Store whose base counts no entry has a coherent index: the empty one. -/
theorem StoreIndexes.of_count_zero (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (dc : Codec.Stream D) {file I S : ByteArray}
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d))
    (h0 : b.indexCount = 0) (hS : b.offset ≤ S.size) :
    StoreIndexes keys c world mark origin dc file I S :=
  ⟨b, n, d, [], hb, h0.symm, by simp, hS, fun _ hi => absurd hi (by simp), trivial⟩

/-- **A Store whose `index.log` is empty has a coherent index** (genesis, import and a follower's
adopted base all write an empty one): whenever the one open succeeds over it. -/
theorem StoreIndexes.of_open_empty (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (dc : Codec.Stream D) (file S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file S.size ByteArray.empty.size
      (segReader ByteArray.empty) (segReader S)) = .ok o) :
    StoreIndexes keys c world mark origin dc file ByteArray.empty S := by
  obtain ⟨b, _, _, _, _, _, hb, hlen, _, _, _, _, hi, _, _, _, _⟩ :=
    openWith_seg_ok keys c world mark origin step file ByteArray.empty S h
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have heb : 0 < entryBytes keys := by unfold entryBytes; omega
  simp only [ByteArray.size_empty, Nat.le_zero, Nat.mul_eq_zero] at hi
  exact StoreIndexes.of_count_zero keys c world mark origin dc hb (hi.resolve_right (by omega)) (by omega)

theorem Entry.read_extract_append {keys : Keys} {I x : ByteArray} {L : List Entry} {i : Nat}
    (hi : i < L.length) (hI : L.length * entryBytes keys ≤ I.size) :
    (I ++ x).extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys) =
      I.extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys) := by
  have : (i + 1) * entryBytes keys ≤ L.length * entryBytes keys := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this
  exact extract_append_le (by omega)

/-- **Appending keeps the index coherent**: records appended to the segment and entries (or
orphans) appended to `index.log` leave every entry the base counts, and the run to the base, as
they were. -/
theorem StoreIndexes.append {keys : Keys} {c : Cadence} {world : Codec.Stream W}
    {mark : W → Nat × ByteArray} {origin : W → ByteArray} {dc : Codec.Stream D} {file I S : ByteArray}
    (x y : ByteArray) (h : StoreIndexes keys c world mark origin dc file I S) :
    StoreIndexes keys c world mark origin dc file (I ++ x) (S ++ y) := by
  obtain ⟨b, n, d, L, hb, hc, hI, hS, hr, hL⟩ := h
  refine ⟨b, n, d, L, hb, hc, by rw [size_append]; omega, by rw [size_append]; omega,
    fun i hi => by rw [Entry.read_extract_append hi hI]; exact hr i hi, ?_⟩
  exact Indexes.congr (fun i j hj => (extract_append_le (by simp only at hj; omega)).symm) L hL

/-- **The writer's cut keeps the index coherent**: `openWriter` truncates the segment to the open's
valid end and `index.log` to the entries the base counts (`Host.openWriter`); the cut Store has
the same coherent index. -/
theorem StoreIndexes.cut_open (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {dc : Codec.Stream D} (file I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file S.size I.size (segReader I) (segReader S)) = .ok o)
    (hS : StoreIndexes keys c world mark origin dc file I S) :
    StoreIndexes keys c world mark origin dc file (I.extract 0 (o.sealed.index.count * entryBytes keys))
      (S.extract 0 o.pos.offset) := by
  obtain ⟨b, n, d, L, hb, hc, hI, hSz, hr, hL⟩ := hS
  obtain ⟨b', _, _, _, op, _, hb', hlen, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  dsimp only
  rw [← hc]
  refine ⟨b, n, d, L, hb, hc, by simp only [size_extract]; omega, by simp only [size_extract]; omega,
    fun i hi => ?_, ?_⟩
  · have : (i + 1) * entryBytes keys ≤ L.length * entryBytes keys := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    rw [extract_prefix I (by omega)]; exact hr i hi
  · exact Indexes.congr (fun i j hj => (extract_prefix S (by simp only at hj; omega)).symm) L hL

theorem entryBytes_forStore (keys : Keys) (sid : ByteArray) :
    entryBytes (keys.forStore sid) = entryBytes keys := rfl

/-- **A seal keeps the index coherent** (the completeness side, discharged at seal): the seal of
an opened World at the open's position, with the entries since the base (what both checkpoints
write, `Base.seal`), over a Store whose index is coherent, leaves a Store (the new base, `index.log`
with the seal's entries appended, the segment cut at the open's position) whose index is coherent:
the old base's entries, then the open's (`openWith_indexes`), each read back at its position
(`run_read`). Premises are `sealed_opens`' and `hstep`. -/
theorem sealed_indexes (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file₀ I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world) {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size = .ok (page, ix', file))
    (hS : StoreIndexes keys c world mark origin dc file₀ I S) :
    StoreIndexes keys c world mark origin dc file (I ++ page) (S.extract 0 o.pos.offset) := by
  obtain ⟨-, hrd, -, hle, -, -, hI, hcnt, -, hsz, -⟩ :=
    seal_facts keys c world mark origin step hw horigin hmono hcap file₀ I S h hP hseal
  obtain ⟨b, n, d, L, hb, hc, hIL, -, hr, hL⟩ := hS
  have hL' := openWith_indexes keys c world mark origin step hstep file₀ I S h hb hL
  obtain ⟨b', _, _, _, _, _, hb', _, _, _, _, _, _, _, _, _, ho⟩ :=
    openWith_seg_ok keys c world mark origin step file₀ I S h
  rw [hb] at hb'; cases hb'
  have hcount : o.sealed.index.count = L.length := by rw [ho]; exact hc.symm
  obtain ⟨b'', _, _, rs, hb'', hf, -⟩ := openWith_world keys c world mark origin step file₀ I S h
  rw [hb] at hb''; cases hb''
  have hor : origin o.opened.world = origin b.world := foldlM_origin horigin rs _ _ hf
  obtain ⟨-, hent, -⟩ := seal_at_end _ _ _ _ _ _ _ _ hseal
  obtain ⟨hfit, -, -, hp, -, -⟩ := entries_ok hent
  have hes : (sealEntries o.index).toList = o.index.toList := by simp [sealEntries]
  rw [hes] at hp hfit
  have hL'' : Indexes dc keys.segment c.recordBytesMax
      (fun x y => (pure ((S.extract 0 o.pos.offset).extract x (x + y)) : Id ByteArray))
      (L ++ o.index.toList) (o.pos.offset, (mark o.opened.world).1) :=
    Indexes.congr (fun i j (hj : j ≤ o.pos.offset) => (extract_prefix S hj).symm) _ hL'
  refine ⟨_, _, _, L ++ o.index.toList, hrd, ?_, ?_, ?_, ?_, hL''⟩
  · simp only [List.length_append, Array.length_toList]; omega
  · rw [hsz, hcnt, hcount]; simp only [List.length_append, Array.length_toList]; exact Nat.le_refl _
  · dsimp only; simp only [size_extract]; omega
  · intro i hi
    dsimp only
    by_cases hiL : i < L.length
    · rw [Entry.read_extract_append hiL hIL, List.getElem_append_left hiL, hor]; exact hr i hiL
    · obtain ⟨j, rfl⟩ : ∃ j, i = L.length + j := ⟨i - L.length, by omega⟩
      have hj : j < o.index.toList.length := by simp only [List.length_append] at hi; omega
      have hpos : (L.length + j) * entryBytes keys = I.size + j * entryBytes keys := by
        rw [hI, hcount, Nat.add_mul]
      rw [hpos, show I.size + j * entryBytes keys + entryBytes keys =
          I.size + (j * entryBytes keys + entryBytes keys) by omega, extract_append_size_add' rfl, hp,
        List.getElem_append_right (by omega)]
      have hr' := run_read (keys.forStore (origin o.opened.world)) o.sealed.index.count o.index.toList j hj hfit
      rw [entryBytes_forStore, show o.sealed.index.count + j = L.length + j by rw [hcount]] at hr'
      simp only [Nat.add_sub_cancel_left]
      exact hr'

end Nanodregg.Host

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Codec ByteArray

/-- The deployed reopen's step decodes its record to the steps it takes: the step count moves by
their number (`openWith_indexes`' `hstep`). -/
theorem foldStep_decode {w w' : World D} {r : ByteArray} (h : foldStep w r = .ok w') :
    ∃ ts : List (Step D × D), (Record.codec Codec.Deployed.digestCodec).decode r = .ok ts ∧
      (recorder.mark w').1 = (recorder.mark w).1 + ts.length := by
  obtain ⟨ps, hd, hr⟩ := Record.step_rooted (dc := Codec.Deployed.digestCodec) (admit := World.step X.env)
    (root := World.roots X.env) h
  exact ⟨ps, hd, by rw [recorder_mark, recorder_mark]; exact rooted_steps hr⟩

/-- The deployed index is coherent: what `page_nonempty` assumes, and every deployed Store
write keeps (`genesis_indexes`, `import_indexes`, `StoreIndexes.append`, `StoreIndexes.cut_open`,
`sealed_indexes_deployed`). -/
abbrev Coherent (keys : Keys) (file I S : ByteArray) : Prop :=
  StoreIndexes keys c world recorder.mark originChain Codec.Deployed.digestCodec file I S

theorem coherent_reader {keys : Keys} {file I S : ByteArray} {o : Opening (World D)}
    (hS : Coherent keys file I S)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    ∃ L : List Entry, L.length = o.sealed.index.count + o.index.size ∧
      Page.Indexes Codec.Deployed.digestCodec keys.segment c.recordBytesMax
        (fun x y => (pure (S.extract x (x + y)) : Id ByteArray)) L (o.pos.offset, (recorder.mark o.opened.world).1) ∧
      ∀ k e, Page.entryAt (m := Id) (keys.forStore (originChain o.opened.world))
        (fun x y => pure (I.extract x (x + y))) o.sealed.index.count o.index k = .ok e → L[k]? = some e := by
  obtain ⟨b, n, d, L, hb, hc, -, -, hr, hL⟩ := hS
  have hL' := openWith_indexes keys c world recorder.mark originChain foldStep
    (fun _ _ _ hs => foldStep_decode hs) file I S h hb hL
  obtain ⟨b', _, _, _, _, _, hb', _, _, _, _, _, _, _, _, _, ho⟩ :=
    openWith_seg_ok keys c world recorder.mark originChain foldStep file I S h
  rw [hb] at hb'; cases hb'
  have hcount : o.sealed.index.count = L.length := by rw [ho]; exact hc.symm
  obtain ⟨b'', _, _, rs, hb'', hf, -⟩ := openWith_world keys c world recorder.mark originChain foldStep file I S h
  rw [hb] at hb''; cases hb''
  have hor : originChain o.opened.world = originChain b.world :=
    foldlM_origin (fun _ _ _ hs => foldStep_originChain hs) rs _ _ hf
  refine ⟨L ++ o.index.toList, by simp only [List.length_append, Array.length_toList]; omega, hL', ?_⟩
  intro k e hk
  rcases Page.entryAt_ok (rd := fun x y => I.extract x (x + y)) hk with ⟨hlt, hre⟩ | ⟨hge, hm⟩
  · rw [hcount] at hlt
    rw [hor, entryBytes_forStore, hr k hlt] at hre
    rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
    exact hre
  · rw [List.getElem?_append_right (by omega), ← hcount, Array.getElem?_toList]
    exact hm

/-- **A page short of the tip is non-empty, at the deployed instance** (HOST-60's lift, cv
01a15180-9499). Over a Store whose index is coherent (`Coherent`: every deployed write keeps it),
the deployed open's state (the resident a writer or a follower starts from), and the deployed
pager (`Host.Deployed.pager`'s `log` arm over bytes: `Page.build` with `Page.entryAt` over the
base's entries on disk and the open's since, the durable end, the World's mark), every page served
from a `start` below the World's step count holds at least one event. -/
theorem page_nonempty (keys : Keys) (file I S : ByteArray) {o : Opening (World D)}
    (hS : Coherent keys file I S)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {start : Nat} (hs : start < o.opened.world.steps) {a : Page.Acc}
    (ha : Id.run (Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain o.opened.world)) (fun x y => pure (I.extract x (x + y)))
        o.sealed.index.count o.index)
      (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) start) = .ok a) :
    0 < a.events.size := by
  obtain ⟨L, hlen, hL, hget⟩ := coherent_reader hS h
  rw [← hlen] at ha
  exact Page.build_nonempty Codec.Deployed.digestCodec_lawful.on Page.budget_fits_event hget hL hs ha

/-- **A deployed page is refused `beforeLog` only from below the entry its search reads first**
(HOST-61's entry-0 case): the deployed pager over any `index.log` and any loop entries, when it
holds an entry and reads entry 0 as `e₀`, refuses `beforeLog` only from a `start` below `e₀`'s step
count. Not proved: that entry 0 is the Store's first record, at step 0 for a Store genesis made and
at the import's step for an imported one (`StoreIndexes` ties each entry to a record, not entry 0
to the first one after the origin frame). -/
theorem page_beforeLog_first (keys : Keys) (I S : ByteArray) (r : Resident (World D)) {start x y : Nat}
    (hc : r.sealed.index.count + r.index.size ≠ 0)
    (ha : Id.run (Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain r.world)) (fun x y => pure (I.extract x (x + y)))
        r.sealed.index.count r.index)
      (r.sealed.index.count + r.index.size) r.pos.offset (recorder.mark r.world) start) =
        .error (.beforeLog x y))
    {e₀ : Entry} (h0 : Page.entryAt (m := Id) (keys.forStore (originChain r.world))
      (fun x y => pure (I.extract x (x + y))) r.sealed.index.count r.index 0 = .ok e₀) :
    start < e₀.steps :=
  Page.build_beforeLog_first hc h0 (fun k x' y' hk => by
    have := Page.entryAt_error (rd := fun x y => I.extract x (x + y)) hk
    cases this) ha

/-- `sealed_indexes` at the deployed instance: every premise discharged as in
`sealed_opens_deployed`. -/
theorem sealed_indexes_deployed (keys : Keys) (file₀ I S : ByteArray) {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file₀ S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (originChain o.opened.world)) c world o.opened.world o.pos
      o.sealed.index (sealEntries o.index) I.size = .ok (page, ix', file))
    (hS : Coherent keys file₀ I S) :
    Coherent keys file (I ++ page) (S.extract 0 o.pos.offset) :=
  sealed_indexes keys c world recorder.mark originChain foldStep
    (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    (fun _ _ _ hs => foldStep_originChain hs) (fun _ _ _ hs => foldStep_steps hs) (by decide)
    (fun _ _ _ hs => foldStep_decode hs) file₀ I S h (openWith_codecFits h) hseal hS

/-- **`host genesis`'s Store has a coherent index**: it holds none. -/
theorem genesis_indexes (keys : Keys) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w₀ : World D}
    (hg : Receive.genesis X name nonce allowance founders = .ok w₀) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    Coherent keys img.base img.index img.segment := by
  obtain ⟨o, ho, -⟩ := genesis_reopens keys hg h
  obtain ⟨_, -, rfl⟩ := genesisImage_ok h
  exact StoreIndexes.of_open_empty keys c world recorder.mark originChain foldStep _ _ _ ho

/-- **`host import`'s Store has a coherent index**: it holds none (a page before its World's step
is refused `beforeLog`, `Page.build_beforeLog_none`). -/
theorem import_indexes (keys : Keys) {name nonce : ByteArray} {want : Codec.Digest} {f : ByteArray}
    {r : Carry.Read D} {w₀ : World D}
    (hi : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r)) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    Coherent keys img.base img.index img.segment := by
  obtain ⟨o, ho, -⟩ := import_reopens keys hi h
  obtain ⟨_, -, rfl⟩ := genesisImage_ok h
  exact StoreIndexes.of_open_empty keys c world recorder.mark originChain foldStep _ _ _ ho

end Nanodregg.Host.Deployed
