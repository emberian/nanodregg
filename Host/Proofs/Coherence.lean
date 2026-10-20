/-
# Host.Proofs.Coherence — every index entry points at its own record (cv 01a15180-9499)

the index file and the loop's entries since the base hold one entry per record: the step count and
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
* `StoreIndexes` (`Host.Proofs.StoreIndex`) — the Store's: the entries the base counts read back
  at their positions under the Store's index key and are a coherent run to the base
  (`Deployed.Coherent` at the deployed instance).

The open checks the one entry it reads (HOST-63, `lastFrameFault`):
* `openWith_lastFrame` — an open that succeeds over a base counting an entry found that entry's
  offset holding a frame a page reads, ending exactly at the base's offset (the last record before
  the base, as far as the sealer's tags are unforgeable). `lastFrameFault_past` and `lastFrame_short` are its teeth (an entry at or past its base;
  a frame that ends before the base), and host-sim `plant-index-offset` refuses an entry one byte
  off its record `indexCorrupt`;
* `lastFrameFault_frame` / `lastFrameFault_sound` — the check passes exactly on such a frame;
  `indexed_last` — the last entry an open's fold makes is one, so a seal of the open passes it
  (`Host.seal_facts`).

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

Every Store written at an open is coherent (the completeness side, in `Host.Proofs.StoreIndex`):
* `openWith_indexes` — the open's entries since the base continue the base's run to the open's
  position and World (`indexed_indexes`: each entry `Host.indexed` makes is the frame the open
  verified);
* `StoreIndexes.of_open_empty` — a Store with an empty the index file (genesis, import, a follower's
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
  entries, so a Store last sealed there is coherent only through that unproved push, and the open's
  last-entry check (`lastFrameFault`, HOST-63) passes on such a base only through it too:
  `seal_facts` proves it for a seal straight after an open, so a wrong push makes the Store refuse
  `indexCorrupt` at its next open;
* that an entry's chain is the chain before its record: `Indexes` pins the offset and the step
  count, not `e.chain` (from which a page states its chain). A wrong chain field is caught by the
  follower's chain check, not here;
* that entry 0 is the Store's first record (see `Deployed.page_beforeLog_first`).
-/
import Host.Proofs.Page
import Host.Proofs.Backup

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
    {endOff now start : Nat} (hB : Protocol.Bounds.pageEventBytesMax + 4 ≤ budget) (hs : start < now) :
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
`pageEventBytesMax + 4`, `budget_fits_event` for the deployed one). The tooth is
`build_empty_incoherent`. -/
theorem build_nonempty [Ord D] [DecidableEq D] {dc : Codec.Stream D} {PD : D → Prop} (hd : Codec.Stream.LawfulOn PD dc)
    {E : Kernel.Env D} {digestOf : ByteArray → Option D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {get : Nat → Id (Except Fault Entry)} {endOff : Nat}
    {now : Nat × ByteArray} {start : Nat} {a : Acc} {L : List Entry}
    (hB : Protocol.Bounds.pageEventBytesMax + 4 ≤ budget)
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

/-! ## The open's check of the base's last entry (HOST-63) -/

/-- **The last entry an indexed fold makes is the frame that ends where the fold ends**: over a
segment holding `encodeAll s prev rs` at `off`, after the 32 bytes `prev`, a fold of at least one
record pushes, last, an entry at or past `off` whose offset holds the last record's frame, chained
from the 32 bytes before it, ending at the fold's offset. -/
theorem indexed_last {W F : Type} {s : Sealer} {rm : Nat} {S : ByteArray}
    (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) :
    ∀ (rs : List ByteArray) (w : W) (idx : Array Entry) (off : Nat) (prev : ByteArray)
      {st : W × Array Entry × Nat}, rs ≠ [] →
      (∀ r ∈ rs, r.size ≤ rm ∧ r.size < 2 ^ 32) →
      S.extract (off - tagBytes) (off - tagBytes + tagBytes) = prev →
      S.extract off (off + (encodeAll s prev rs).size) = encodeAll s prev rs →
      rs.foldlM (indexed mark step) (w, idx, off) = .ok st →
      ∃ (e : Entry) (r : ByteArray), st.2.1.back? = some e ∧ off ≤ e.offset ∧ r.size ≤ rm ∧ r.size < 2 ^ 32 ∧
        S.extract e.offset (e.offset + frameSize r) =
          frame s (S.extract (e.offset - tagBytes) (e.offset - tagBytes + tagBytes)) r ∧
        e.offset + frameSize r = st.2.2
  | [], _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | r :: rs, w, idx, off, prev, st, _, hb, hp, he, h => by
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
      cases rs with
      | nil =>
        simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨⟨a, off, ch⟩, r, by simp, Nat.le_refl _, (hb r (by simp)).1, (hb r (by simp)).2, ?_, rfl⟩
        rw [hp]; exact he1
      | cons r' rs' =>
        have hp2 : S.extract (off + frameSize r - tagBytes) (off + frameSize r - tagBytes + tagBytes) =
            s.tag (prev ++ r) := by
          obtain ⟨-, -, f2⟩ := frame_fields s prev r ByteArray.empty
          rw [ByteArray.append_empty] at f2
          rw [← f2, ← he1, extract_extract]
          unfold frameSize
          congr 1 <;> omega
        obtain ⟨e, r₀, hback, hge, h1, h2, h3, h4⟩ := indexed_last mark step (r' :: rs') w' (idx.push ⟨a, off, ch⟩)
          (off + frameSize r) (s.tag (prev ++ r)) (by simp) (fun x hx => hb x (by simp [hx])) hp2 he2 h
        exact ⟨e, r₀, hback, by have := Page.frameSize_pos r; omega, h1, h2, h3, h4⟩



theorem frameAt_bounds {s : Sealer} {rm : Nat} {log prev : ByteArray} {off : Nat} {rd : Read}
    (h : frameAt s rm log off prev = some rd) : rd.record.size ≤ rm ∧ rd.record.size < 2 ^ 32 := by
  unfold frameAt at h
  split at h
  · cases h
  · rename_i len hl
    split at h
    · cases h
    · rename_i hlen
      split at h
      · cases h
      · rename_i hfit
        dsimp only at h
        split at h
        · cases h
          simp only [size_extract]
          have := lenAt_lt hl
          constructor <;> omega
        · cases h

/-- **The open's last-entry check passes on the frame that ends at the base**: an entry past the
segment's first 32 bytes whose offset holds a frame, chained from the 32 bytes before it and within the
record bound, that ends at `B` (inside the segment). -/
theorem lastFrameFault_frame {F : Type} {s : Sealer} {rm B : Nat} {S r : ByteArray} {e : Entry}
    (h32 : tagBytes ≤ e.offset) (hB : e.offset + frameSize r = B) (hBS : B ≤ S.size)
    (hf : S.extract e.offset (e.offset + frameSize r) = frame s (S.extract (e.offset - tagBytes) e.offset) r)
    (hr : r.size ≤ rm) (hr32 : r.size < 2 ^ 32) :
    Id.run (lastFrameFault (F := F) s rm B (some e) (segReader S)) = none := by
  have hfs := frameSize_ge r
  have hlr : lastRange rm B e = some (e.offset - tagBytes, B - e.offset + tagBytes) := by
    unfold lastRange
    rw [if_pos ⟨h32, by omega, by unfold frameMax; unfold frameSize at hB; omega⟩]
  have hpz : (S.extract (e.offset - tagBytes) e.offset).size = tagBytes := by rw [size_extract]; omega
  have hread : S.extract (e.offset - tagBytes) (e.offset - tagBytes + (B - e.offset + tagBytes)) =
      S.extract (e.offset - tagBytes) e.offset ++ frame s (S.extract (e.offset - tagBytes) e.offset) r := by
    rw [show e.offset - tagBytes + (B - e.offset + tagBytes) = B by omega,
      extract_eq_extract_append_extract e.offset (by omega) (by omega), ← hB, hf]
  have hfa := frameAt_frame s (recordMax := rm) (S.extract (e.offset - tagBytes) e.offset)
    (S.extract (e.offset - tagBytes) e.offset) r ByteArray.empty hr hr32
  rw [ByteArray.append_empty, hpz] at hfa
  simp only [lastFrameFault, hlr, segReader, bind, pure]
  rw [hread, if_neg (by rw [size_append, hpz, size_frame]; unfold frameSize at hB; omega)]
  unfold lastFrame
  rw [extract_append_eq_left hpz.symm, hfa]
  simp only [size_append, hpz, size_frame, if_true, Option.map_none]
  rfl

/-- **What the open's last-entry check found** (the converse): when it passes for entry `e` over a
segment, `e`'s offset is at least 32 bytes into the segment and holds a frame a page reads (`frameOf`)
that ends exactly at `B`. -/
theorem lastFrameFault_sound {F : Type} {s : Sealer} {rm B : Nat} {S : ByteArray} {e : Entry}
    (h : Id.run (lastFrameFault (F := F) s rm B (some e) (segReader S)) = none) :
    tagBytes ≤ e.offset ∧ ∃ r, frameOf s rm (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) e.offset = some r ∧
      e.offset + frameSize r = B := by
  simp only [lastFrameFault] at h
  cases hlr : lastRange rm B e with
  | none => rw [hlr] at h; cases h
  | some p =>
    obtain ⟨a, len⟩ := p
    obtain ⟨h32, hlt, hmax, rfl, rfl⟩ := lastRange_some hlr
    rw [hlr] at h
    simp only [segReader, bind, pure] at h
    generalize hfb : S.extract (e.offset - tagBytes) (e.offset - tagBytes + (B - e.offset + tagBytes)) = fb at h
    have hfbs : fb.size = min (e.offset - tagBytes + (B - e.offset + tagBytes)) S.size - (e.offset - tagBytes) := by
      rw [← hfb, size_extract]
    by_cases hsz : fb.size = B - e.offset + tagBytes
    · rw [if_neg (fun hn => hn hsz)] at h
      cases hfa : frameAt s rm fb tagBytes (fb.extract 0 tagBytes) with
      | none => simp only [lastFrame, hfa, Option.map_some] at h; cases h
      | some rd =>
        have hnext : rd.next = fb.size := by
          refine Classical.byContradiction fun hne => ?_
          simp only [lastFrame, hfa, if_neg hne, Option.map_some] at h
          cases h
        obtain ⟨-, -, hx, -⟩ := frameAt_some hfa
        obtain ⟨hr, hr32⟩ := frameAt_bounds hfa
        rw [hnext, hsz] at hx
        have hsz2 := congrArg ByteArray.size hx
        rw [size_frame, size_extract, hsz] at hsz2
        have hfs : frameSize rd.record = B - e.offset := by unfold frameSize; omega
        refine ⟨h32, rd.record, ?_, by omega⟩
        have e1 : fb.extract tagBytes (B - e.offset + tagBytes) = S.extract e.offset (e.offset + frameSize rd.record) := by
          rw [← hfb, extract_extract, hfs]; congr 1 <;> omega
        have e2 : fb.extract 0 tagBytes = S.extract (e.offset - tagBytes) (e.offset - tagBytes + tagBytes) := by
          rw [← hfb, extract_extract]; congr 1 <;> omega
        rw [e1, e2] at hx
        exact frameOf_frame rfl hx hr hr32
    · rw [if_pos hsz] at h; cases h

/-- **The tooth of the last-entry check**: an entry at or past its base's offset (it names no
record before the base, HOST-53's alternative (d)) is refused `indexCorrupt`, before anything is
read. -/
theorem lastFrameFault_past {F : Type} {m : Type → Type} [Monad m] (s : Sealer) (rm B : Nat) (e : Entry)
    (readTail : Nat → Nat → m (Except (StoreFault F) ByteArray)) (h : B ≤ e.offset) :
    lastFrameFault s rm B (some e) readTail = pure (some (.base .indexCorrupt)) := by
  simp only [lastFrameFault, lastRange]
  rw [if_neg (by omega)]

/-- **The tooth of `lastFrame`**: a frame that verifies but ends before the bytes do (an entry
pointing at an earlier record, not the last before the base) is refused `indexCorrupt`. -/
theorem lastFrame_short {s : Sealer} {rm : Nat} {bytes : ByteArray} {rd : Read}
    (h : frameAt s rm bytes tagBytes (bytes.extract 0 tagBytes) = some rd) (hn : rd.next ≠ bytes.size) :
    lastFrame s rm bytes = some .indexCorrupt := by
  unfold lastFrame
  rw [h]
  simp only [if_neg hn]

/-- **The one entry open reads points at its own record** (HOST-63): an open that succeeds over a
base that counts an entry read that entry at its position under the Store's index key, and its
offset, at least 32 bytes into the segment, holds a frame a page reads (`frameOf`) that ends exactly at the
base's offset. That this is the segment's own last record, not another frame that verifies there,
rests on the sealer's tags; it is not proved from `Log.recover`. -/
theorem openWith_lastFrame {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hpos : 0 < o.sealed.index.count) :
    ∃ (b : Base W) (n : Nat) (d : ByteArray) (e : Entry) (r : ByteArray),
      Base.read keys c world file = .ok (b, n, d) ∧ b.indexCount = o.sealed.index.count ∧
      b.offset = o.sealed.offset ∧ Entry.read (keys.forStore (origin b.world)) (b.indexCount - 1)
        (I.extract ((b.indexCount - 1) * entryBytes keys) ((b.indexCount - 1) * entryBytes keys + entryBytes keys)) =
          some e ∧
      tagBytes ≤ e.offset ∧
      frameOf keys.segment c.recordBytesMax (fun x y => (pure (S.extract x (x + y)) : Id ByteArray)) e.offset = some r ∧
      e.offset + frameSize r = b.offset := by
  obtain ⟨b, n, d, _, _, _, hb, _, _, _, _, _, _, _, hix, hlf, _, _, ho⟩ :=
    openWith_seg_ok keys c world mark origin step file H I S h
  have hc : b.indexCount = o.sealed.index.count := by rw [ho]
  have hoff : b.offset = o.sealed.offset := by rw [ho]
  have hp : 0 < b.indexCount := by omega
  rcases indexNamed_none hix with ⟨hz, -⟩ | ⟨-, e, he, -, -⟩
  · omega
  · have hle : lastEntry (keys.forStore (origin b.world)) b.indexCount
        (I.extract (lastAt keys b.indexCount).1 ((lastAt keys b.indexCount).1 + (lastAt keys b.indexCount).2)) =
          some e := by
      unfold lastEntry; rw [if_neg (by omega)]; exact he
    rw [hle] at hlf
    obtain ⟨h32, r, hr, hend⟩ := lastFrameFault_sound hlf
    rw [lastAt_read keys _ hp] at he
    exact ⟨b, n, d, e, r, hb, hc, hoff, he, h32, hr, hend⟩

end Nanodregg.Host
