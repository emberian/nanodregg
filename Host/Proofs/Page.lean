/-
# Host.Proofs.Page — a log page always has room for the next event, is never built from an entry that failed, and never holds more steps than one record

`Page.walkStep` stops a page (`full`) when the next event does not fit the budget. At a budget of
`eventBytesMax + 5` (`budget_fits_event` for the deployed one) that never happens to an empty
page: the first record past `start` the walk reads, the page serves from (`walk_serves`), and a
page `build` returns empty was never full and holds no bytes (`build_empty`). It ran out of segment.
That a page short of the tip is non-empty also needs the Store's index-segment coherence, which
this file does not prove (cv 01a15180-9499). PROTOCOL's follow refuses an empty page short of the
tip `badResult`.

HOST-33 (condition 2, never-served): a page meets index entries only through `entryAt`, and is
built from ONE of them, the one `locate` returns.

* `locate_got` — the entry `locate` returns is what its reader returned at that position;
* `entryAt_ok` — what `entryAt` returns from `index.log` read back at its position (its tag
  verified there: `Entry.read_sound`), and past the disk entries is the loop's own;
* `build_located` / `build_never_served` — a page that is served is the walk of the segment from
  that one entry, so no page is built from an entry whose tag failed;
* `build_badIndex` — the tooth: when the first entry a search reads does not read back, the page
  is refused `badIndex 0`, by name.
* `build_beforeLog` / `build_beforeLog_none` — a page from before the Store's log (its first
  record past `start`, or no record under a World past it) is refused `beforeLog`, by name, so a
  page `build` serves is walked from an entry at or below `start` (`build_located`, HOST-61).

A page and the record its follower writes from it (HOST-11 L41: a follower appends one page's
Turns as ONE record, and a record's decode refuses more than `recordTurnsMax` Turns):

* `build_events_le` — every page `build` returns holds at most `recordTurnsMax` events;
* `Record.encode_eq_some` / `Record.encode_none` — `Record.encode` writes exactly the codec's bytes
  for at most `recordTurnsMax` pairs and refuses (`none`) more, which the append path names
  `recordTooLarge`;
* `Record.encode_decode` / `Record.step_encode` — a record `encode` returns decodes back to its
  pairs (each fitting the codec), so the reopen's step over it is the run of those very pairs.

Stated in `Id` over a pure reader; `Host.Deployed.pager` runs the same `build` in `IO` over the
files.
-/
import Host.Page
import Host.Proofs.Index
import Codec.Proofs.World

namespace Nanodregg.Host.Page

/-- **The deployed budget holds every event the codec admits**: an event of `eventBytesMax` bytes
behind its 1-byte tag (`stepEvent`) and the page's 4-byte length (cv 01a150c0: `+ 4` was one short).
`walkTurnsAt_one_short` and `walk_one_short` are the tooth at `+ 4`. -/
theorem budget_fits_event : Kernel.Bounds.eventBytesMax + 5 ≤ budget := by decide

theorem locate_go_got (get : Nat → Id (Except Fault Entry)) (start : Nat) :
    ∀ (fuel lo hi : Nat) (e : Entry), get lo = .ok e → ∀ {k : Nat} {e' : Entry},
      locate.go get start fuel lo hi e = .ok (k, e') → get k = .ok e' := by
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
      · rename_i em hem
        split at hg
        · exact ih _ hi em hem hg
        · exact ih lo _ e he hg

/-- **The entry a search returns is the entry read at its position**: `locate` returns `(k, e)`
only when its reader returned `e` for position `k`. -/
theorem locate_got {get : Nat → Id (Except Fault Entry)} {count start k : Nat} {e : Entry}
    (h : locate get count start = .ok (k, e)) : get k = .ok e := by
  simp only [locate, bind] at h
  split at h
  · simp only [pure] at h; cases h
  · rename_i e₀ he₀
    exact locate_go_got get start count 0 count e₀ he₀ h

/-- What `entryAt` returns: from `index.log`, an entry that read back at its own position under
the Store's key; past the `disk` entries, the loop's own entry. -/
theorem entryAt_ok {keys : Keys} {rd : Nat → Nat → ByteArray} {disk : Nat} {mem : Array Entry} {k : Nat}
    {e : Entry} (h : entryAt (m := Id) keys (fun o l => pure (rd o l)) disk mem k = .ok e) :
    (k < disk ∧ Entry.read keys k (rd (k * entryBytes keys) (entryBytes keys)) = some e) ∨
      (disk ≤ k ∧ mem[k - disk]? = some e) := by
  simp only [entryAt] at h
  split at h
  · rename_i hk
    simp only [bind, pure] at h
    split at h
    · rename_i e' he'
      cases h; exact Or.inl ⟨hk, he'⟩
    · cases h
  · rename_i hk
    split at h
    · rename_i e' he'
      simp only [pure] at h
      cases h; exact Or.inr ⟨by omega, he'⟩
    · simp only [pure] at h; cases h

/-- **A served page is built from ONE located entry**: either it is the empty page at `now` (nothing
after `start`, or no index), or `locate` returned entry `k` (read through `get` at `k`), its chain is
a digest, and the page is `walk` of the segment from that entry's offset and chain. -/
theorem build_located {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {digestOf : ByteArray → Option D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {get : Nat → Id (Except Fault Entry)} {count endOff : Nat}
    {now : Nat × ByteArray} {start : Nat} {a : Acc}
    (h : build E dc digestOf s recordMax budget read get count endOff now start = .ok a) :
    (now.1 ≤ start ∧ a = ⟨#[], 0, now.1, now.2, false⟩) ∨
      ∃ k e c, locate get count start = .ok (k, e) ∧ get k = .ok e ∧ e.steps ≤ start ∧
        digestOf e.chain = some c ∧
        walk E dc s recordMax budget read endOff start (count - k) e.offset c
          { steps := e.steps, chain := e.chain } = .ok a := by
  simp only [build] at h
  split at h
  · rename_i hc
    simp only [pure] at h; cases h; exact Or.inl ⟨hc, rfl⟩
  · split at h
    · simp only [pure] at h; cases h
    · simp only [bind] at h
      split at h
      · simp only [pure] at h; cases h
      · rename_i k e hl
        split at h
        · simp only [pure] at h; cases h
        · rename_i hle
          split at h
          · simp only [pure] at h; cases h
          · rename_i c hd
            exact Or.inr ⟨k, e, c, hl, locate_got hl, Nat.not_lt.mp hle, hd, h⟩

/-- **No page is built from an entry whose tag failed** (HOST-33, condition 2). A page `build`
serves over `entryAt` (the deployed pager's getter) after `start` is the walk of the segment from
ONE entry `e` at position `k`: from `index.log`, the bytes at `k` are EXACTLY `Entry.bytes keys k e`
(the entry with its tag over `k`, `Entry.read_sound`); past the disk entries, it is the loop's own.
An entry whose tag failed is never returned by `entryAt`, so it never reaches a page. -/
theorem build_never_served {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {digestOf : ByteArray → Option D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {keys : Keys} {rd : Nat → Nat → ByteArray} {disk : Nat}
    {mem : Array Entry} {count endOff : Nat} {now : Nat × ByteArray} {start : Nat} {a : Acc}
    (h : build E dc digestOf s recordMax budget read (entryAt keys (fun o l => pure (rd o l)) disk mem)
      count endOff now start = .ok a) (hs : start < now.1) :
    ∃ k e c,
      ((k < disk ∧ Entry.bytes keys k e = rd (k * entryBytes keys) (entryBytes keys)) ∨
        (disk ≤ k ∧ mem[k - disk]? = some e)) ∧
      digestOf e.chain = some c ∧
      walk E dc s recordMax budget read endOff start (count - k) e.offset c
        { steps := e.steps, chain := e.chain } = .ok a := by
  rcases build_located h with ⟨hc', _⟩ | ⟨k, e, c, _, hg, _, hd, hw⟩
  · omega
  · refine ⟨k, e, c, ?_, hd, hw⟩
    rcases entryAt_ok hg with ⟨hk, hr⟩ | hm
    · exact Or.inl ⟨hk, Entry.read_sound hr⟩
    · exact Or.inr hm

/-- **The tooth of `build_never_served`**: when entry 0 is on disk and does not read back at its
position (the first entry every search reads), a page after `start` is refused `badIndex 0` by name. -/
theorem build_badIndex {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) (dc : Codec.Stream D)
    (digestOf : ByteArray → Option D) (s : Log.Sealer) (recordMax budget : Nat)
    (read : Nat → Nat → Id ByteArray) (keys : Keys) (rd : Nat → Nat → ByteArray) (disk : Nat)
    (mem : Array Entry) (count endOff : Nat) (now : Nat × ByteArray) (start : Nat)
    (hs : start < now.1) (hc : count ≠ 0) (hd : 0 < disk)
    (hr : Entry.read keys 0 (rd 0 (entryBytes keys)) = none) :
    build E dc digestOf s recordMax budget read (entryAt keys (fun o l => pure (rd o l)) disk mem)
      count endOff now start = .error (.badIndex 0) := by
  simp only [build, locate, entryAt, bind, pure, Nat.zero_mul, if_pos hd, hr]
  rw [if_neg (by omega), if_neg hc]

/-! ## A page holds at most one record's steps -/

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (h : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_inv P f h l (f b a) (h b a hb)

/-- One record's walk never takes a page past `recordTurnsMax` events. -/
theorem walkTurnsAt_events_le {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) (budget start : Nat)
    (chain₀ : D) (h₀ : Nat) (ts : List (Kernel.Step D × D)) (acc : Acc)
    (h : acc.events.size ≤ recordTurnsMax) :
    (walkTurnsAt E budget start chain₀ h₀ ts acc).1.events.size ≤ recordTurnsMax := by
  unfold walkTurnsAt
  refine foldl_inv (fun st : Acc × D × Nat => st.1.events.size ≤ recordTurnsMax) _ ?_ ts _ h
  rintro ⟨a, c, k⟩ ⟨t, root⟩ hb
  simp only at hb
  simp only [walkStep]
  split
  · exact hb
  · split
    · exact hb
    · split
      · exact hb
      · rename_i hn
        simp only [Array.size_push]
        omega

theorem walk_events_le {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {s : Log.Sealer} {recordMax budget : Nat} {read : Nat → Nat → Id ByteArray} {endOff start : Nat} :
    ∀ (fuel off : Nat) (c : D) (acc a : Acc), acc.events.size ≤ recordTurnsMax →
      walk E dc s recordMax budget read endOff start fuel off c acc = .ok a →
      a.events.size ≤ recordTurnsMax := by
  intro fuel
  induction fuel with
  | zero =>
    intro off c acc a hacc h
    simp only [walk, pure] at h
    cases h; exact hacc
  | succ fuel ih =>
    intro off c acc a hacc h
    simp only [walk, bind, pure] at h
    split at h
    · cases h; exact hacc
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
        · exact ih _ _ _ _ (walkTurnsAt_events_le E budget start c acc.steps _ acc hacc) h

/-- **Every page `build` returns holds at most `recordTurnsMax` events** (HOST-11 L41): a follower
appends one page's steps as one record, so an honest page never asks it to write a record its
reopen refuses on its count. -/
theorem build_events_le {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {digestOf : ByteArray → Option D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {get : Nat → Id (Except Fault Entry)} {count endOff : Nat}
    {now : Nat × ByteArray} {start : Nat} {a : Acc}
    (h : build E dc digestOf s recordMax budget read get count endOff now start = .ok a) :
    a.events.size ≤ recordTurnsMax := by
  rcases build_located h with ⟨_, rfl⟩ | ⟨k, e, c, _, _, _, _, hw⟩
  · show 0 ≤ recordTurnsMax; exact Nat.zero_le _
  · exact walk_events_le _ _ _ _ _ (Nat.zero_le _) hw

/-! ## A page is never stopped for room before it serves (cv 01a150c0)

`walkStep` marks a page `full` when the next event does not fit its budget. Under a budget of
`eventBytesMax + 5` that never happens to a page that holds no event: every event a record decodes
to is at most `eventBytesMax` bytes (`Codec.Kernel.batch_lawfulOn`), and a page carries it behind a
1-byte tag (`stepEvent`) and a 4-byte length.

* `walkTurnsAt_serves` — a record's walk from an empty page serves the first step past `start`;
* `walk_serves` — the first record past `start` that `walk` reads, the page serves from;
* `walk_empty` / `build_empty` — a page that comes back empty was never `full` and holds no bytes:
  it ran out of segment (or fuel) before any step past `start`;
* `walkTurnsAt_one_short` / `walk_one_short` — the tooth: at `+ 4`, a first event of the codec's
  full size leaves the page `full` and EMPTY.

Not proved here: that the segment from the entry `locate` returns holds the step `start + 1` (the
Store's index-segment coherence), which `build_empty` would need to conclude a page short of the tip
is non-empty. -/

/-- **A page's event is at most the codec's bound and its tag**: an event a record decodes to
(`Step.Fits`: a Turn's `event` at most `eventBytesMax`, a refusal's at most `callMax`, the same
number) is at most `eventBytesMax + 1` bytes on a page. -/
theorem stepEvent_size_le {D : Type} {PD : D → Prop} {s : Kernel.Step D}
    (h : Codec.Kernel.Step.Fits PD s) : (stepEvent s).size ≤ Kernel.Bounds.eventBytesMax + 1 := by
  cases s with
  | turn t =>
    have hf : Codec.Kernel.Turn.Fits PD t := h
    have he : t.event.size ≤ Kernel.Bounds.eventBytesMax := hf.2.2.2.2.2.2.2.1
    have hs : (stepEvent (.turn t)).size = t.event.size + 1 := by
      simp only [stepEvent, ByteArray.size_append]; exact Nat.add_comm _ _
    omega
  | refusal r =>
    have hf : Codec.Kernel.Refused.Fits PD r := h
    have he : r.event.size ≤ Kernel.Bounds.eventBytesMax := hf.2.2.2.2.2
    have hs : (stepEvent (.refusal r)).size = r.event.size + 1 := by
      simp only [stepEvent, ByteArray.size_append]; exact Nat.add_comm _ _
    omega

theorem foldl_walkStep_events_ge {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D)
    (budget start : Nat) (ts : List (Kernel.Step D × D)) (st : Acc × D × Nat) :
    st.1.events.size ≤ (ts.foldl (walkStep E budget start) st).1.events.size := by
  refine foldl_inv (fun x : Acc × D × Nat => st.1.events.size ≤ x.1.events.size) _ ?_ ts _
    (Nat.le_refl _)
  rintro ⟨a, c, k⟩ ⟨t, root⟩ hb
  simp only at hb
  simp only [walkStep]
  split
  · exact hb
  · split
    · exact hb
    · split
      · exact hb
      · simp only [Array.size_push]
        omega

/-- A full page walks nothing more. -/
theorem foldl_walkStep_full {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D)
    (budget start : Nat) : ∀ (ts : List (Kernel.Step D × D)) (st : Acc × D × Nat),
      st.1.full = true → ts.foldl (walkStep E budget start) st = st
  | [], _, _ => rfl
  | x :: ts, ⟨a, c, k⟩, hf => by
    rw [List.foldl_cons]
    have : walkStep E budget start (a, c, k) x = (a, c, k) := by
      obtain ⟨t, root⟩ := x
      simp only at hf
      simp only [walkStep, hf, ↓reduceIte]
    rw [this]
    exact foldl_walkStep_full E budget start ts _ hf

/-- What a page that holds no event knows at a point of one record's walk: it is not `full`, it
holds no bytes, its count is the walk's own, and that count is at most `start` or where the walk
began (`h₀`). -/
def EmptyOk {D : Type} (start h₀ : Nat) (st : Acc × D × Nat) : Prop :=
  st.1.events = #[] → st.1.full = false ∧ st.1.bytes = 0 ∧ st.1.steps = st.2.2 ∧ st.2.2 ≤ max start h₀

theorem walkStep_empty {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) {budget : Nat}
    (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) (start h₀ : Nat) (st : Acc × D × Nat)
    (x : Kernel.Step D × D) (hx : (stepEvent x.1).size ≤ Kernel.Bounds.eventBytesMax + 1)
    (h : EmptyOk start h₀ st) : EmptyOk start h₀ (walkStep E budget start st x) := by
  obtain ⟨a, c, k⟩ := st
  obtain ⟨t, root⟩ := x
  unfold EmptyOk at h
  simp only at h hx
  simp only [walkStep]
  split
  · exact h
  · split
    · rename_i hs
      intro he
      obtain ⟨hf, hb, _, _⟩ := h he
      refine ⟨hf, hb, rfl, ?_⟩
      show k + 1 ≤ max start h₀
      omega
    · split
      · rename_i hc
        intro he
        have he' : a.events = #[] := he
        obtain ⟨_, hb, _, _⟩ := h he'
        exfalso
        rcases hc with hc | hc
        · rw [he'] at hc; exact absurd hc (by decide)
        · rw [hb] at hc; omega
      · intro he
        exact absurd (congrArg Array.size he) (by simp)

theorem foldl_walkStep_empty {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) {budget : Nat}
    (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) (start h₀ : Nat) :
    ∀ (ts : List (Kernel.Step D × D)) (st : Acc × D × Nat),
      (∀ p ∈ ts, (stepEvent p.1).size ≤ Kernel.Bounds.eventBytesMax + 1) →
      EmptyOk start h₀ st → EmptyOk start h₀ (ts.foldl (walkStep E budget start) st)
  | [], _, _, h => h
  | x :: ts, st, hs, h =>
    foldl_walkStep_empty E hB start h₀ ts _ (fun p hp => hs p (by simp [hp]))
      (walkStep_empty E hB start h₀ st x (hs x (by simp)) h)

/-- An empty, not full page that walks a record and stays empty skipped every step of it: its
count before the record plus the record's length is at most `start`. -/
theorem foldl_walkStep_empty_count {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D)
    {budget : Nat} (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) (start : Nat) :
    ∀ (ts : List (Kernel.Step D × D)) (a : Acc) (c : D) (k : Nat),
      (∀ p ∈ ts, (stepEvent p.1).size ≤ Kernel.Bounds.eventBytesMax + 1) →
      a.events = #[] → a.bytes = 0 → a.full = false → k ≤ start →
      (ts.foldl (walkStep E budget start) (a, c, k)).1.events = #[] → k + ts.length ≤ start
  | [], _, _, _, _, _, _, _, hk, _ => by simpa using hk
  | (t, root) :: ts, a, c, k, hs, hev, hb, hf, hk, he => by
    rw [List.foldl_cons] at he
    have hx := hs (t, root) (by simp)
    simp only at hx
    by_cases hs1 : k + 1 ≤ start
    · have hw : walkStep E budget start (a, c, k) (t, root) =
          ({ a with steps := k + 1, chain := E.bytes (Kernel.stepLink E c t root) },
            Kernel.stepLink E c t root, k + 1) := by
        simp only [walkStep, hf, Bool.false_eq_true, ↓reduceIte, if_pos hs1]
      rw [hw] at he
      have := foldl_walkStep_empty_count E hB start ts
        { a with steps := k + 1, chain := E.bytes (Kernel.stepLink E c t root) }
        (Kernel.stepLink E c t root) (k + 1) (fun p hp => hs p (by simp [hp])) hev hb hf hs1 he
      simp only [List.length_cons]
      omega
    · exfalso
      have hw : (walkStep E budget start (a, c, k) (t, root)).1.events = a.events.push (stepEvent t) := by
        simp only [walkStep, hf, Bool.false_eq_true, ↓reduceIte, if_neg hs1]
        rw [if_neg (by rw [hev, hb]; simp only [Array.size_empty, recordTurnsMax]; omega)]
      have hge := foldl_walkStep_events_ge E budget start ts (walkStep E budget start (a, c, k) (t, root))
      rw [he, hw] at hge
      simp at hge

/-- **A record's walk from an empty page serves the first step past `start`** whenever the budget
holds `eventBytesMax + 5` and every event in the record is at most `eventBytesMax` (behind its tag):
the walk may first skip steps at or below `start`, and the page may carry an accumulator from records
it skipped whole (no events, no bytes, not full). -/
theorem walkTurnsAt_serves {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) {budget : Nat}
    (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) (start : Nat) (c : D) (h₀ : Nat)
    (ts : List (Kernel.Step D × D)) (acc : Acc)
    (hs : ∀ p ∈ ts, (stepEvent p.1).size ≤ Kernel.Bounds.eventBytesMax + 1)
    (hev : acc.events = #[]) (hb : acc.bytes = 0) (hf : acc.full = false) (hst : h₀ ≤ start)
    (hpast : start < h₀ + ts.length) :
    0 < (walkTurnsAt E budget start c h₀ ts acc).1.events.size := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have := foldl_walkStep_empty_count E hB start ts acc c h₀ hs hev hb hf hst
    (Array.eq_empty_of_size_eq_zero h0)
  omega

/-- **One record's walk never stops an empty page for room**: under the same budget, a page that
holds no event after the record is not `full`, holds no bytes, and its count is at most `start` or
where it began. -/
theorem walkTurnsAt_empty {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) {budget : Nat}
    (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) (start : Nat) (c : D)
    (ts : List (Kernel.Step D × D)) (acc : Acc)
    (hs : ∀ p ∈ ts, (stepEvent p.1).size ≤ Kernel.Bounds.eventBytesMax + 1)
    (hacc : acc.events = #[] → acc.full = false ∧ acc.bytes = 0)
    (he : (walkTurnsAt E budget start c acc.steps ts acc).1.events = #[]) :
    (walkTurnsAt E budget start c acc.steps ts acc).1.full = false ∧
      (walkTurnsAt E budget start c acc.steps ts acc).1.bytes = 0 ∧
      (walkTurnsAt E budget start c acc.steps ts acc).1.steps ≤ max start acc.steps := by
  have h0 : EmptyOk start acc.steps (acc, c, acc.steps) := by
    intro h; exact ⟨(hacc h).1, (hacc h).2, rfl, Nat.le_max_right _ _⟩
  obtain ⟨hf, hb, hst, hk⟩ := foldl_walkStep_empty E hB start acc.steps ts _ hs h0 he
  exact ⟨hf, hb, Nat.le_trans (Nat.le_of_eq hst) hk⟩

/-- **The tooth**: one byte less (`eventBytesMax + 4`, what `budget_fits_event` stated before
cv 01a150c0) and a first event past `start` of the codec's full size leave the record's walk `full`
and EMPTY: nothing after it is served. -/
theorem walkTurnsAt_one_short {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) (start : Nat)
    (c : D) (h₀ : Nat) (t : Kernel.Step D) (root : D) (rest : List (Kernel.Step D × D)) (acc : Acc)
    (hev : acc.events = #[]) (hb : acc.bytes = 0) (hf : acc.full = false)
    (hx : (stepEvent t).size = Kernel.Bounds.eventBytesMax + 1) (hst : start < h₀ + 1) :
    (walkTurnsAt E (Kernel.Bounds.eventBytesMax + 4) start c h₀ ((t, root) :: rest) acc).1.full = true ∧
      (walkTurnsAt E (Kernel.Bounds.eventBytesMax + 4) start c h₀ ((t, root) :: rest) acc).1.events = #[] := by
  have hw : walkStep E (Kernel.Bounds.eventBytesMax + 4) start (acc, c, h₀) (t, root) =
      ({ acc with full := true }, c, h₀) := by
    simp only [walkStep, hf, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by omega), if_pos (Or.inr (by rw [hb, hx]; omega))]
  unfold walkTurnsAt
  rw [List.foldl_cons, hw, foldl_walkStep_full E _ start rest _ rfl]
  exact ⟨rfl, hev⟩

theorem walk_events_ge {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {s : Log.Sealer} {recordMax budget : Nat} {read : Nat → Nat → Id ByteArray} {endOff start : Nat} :
    ∀ (fuel off : Nat) (c : D) (acc a : Acc),
      walk E dc s recordMax budget read endOff start fuel off c acc = .ok a →
      acc.events.size ≤ a.events.size := by
  intro fuel
  induction fuel with
  | zero =>
    intro off c acc a h
    simp only [walk, pure] at h
    cases h; exact Nat.le_refl _
  | succ fuel ih =>
    intro off c acc a h
    simp only [walk, bind, pure] at h
    split at h
    · cases h; exact Nat.le_refl _
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
        · exact Nat.le_trans (foldl_walkStep_events_ge E budget start _ (acc, c, acc.steps)) (ih _ _ _ _ h)

/-- A full page is returned as it is. -/
theorem walk_full {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {s : Log.Sealer} {recordMax budget : Nat} {read : Nat → Nat → Id ByteArray} {endOff start : Nat}
    (fuel off : Nat) (c : D) (acc : Acc) (hf : acc.full = true) :
    walk E dc s recordMax budget read endOff start fuel off c acc = .ok acc := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [walk, hf, Bool.true_or, ↓reduceIte, pure]

/-- The steps of a record `walk` decodes: each is in the codec's domain, so its event on a page is at
most `eventBytesMax + 1` bytes. -/
theorem decode_stepEvent_le {D : Type} {PD : D → Prop} {dc : Codec.Stream D}
    (hd : Codec.Stream.LawfulOn PD dc) {r : ByteArray} {ts : List (Kernel.Step D × D)}
    (hdec : (Record.codec dc).decode r = .ok ts) :
    ∀ p ∈ ts, (stepEvent p.1).size ≤ Kernel.Bounds.eventBytesMax + 1 := fun p hp =>
  stepEvent_size_le
    (((Codec.Kernel.batch_lawfulOn hd recordTurnsMax (by decide)).eq_bytes_of_decode hdec).1.2 p hp).1

/-- **A page `walk` returns empty was never stopped for room** (cv 01a150c0, the lift through the
segment): with the digest codec lawful and a budget of `eventBytesMax + 5`, a page that holds no
event is not `full`, holds no bytes, and its count is at most `start` or where the walk began. -/
theorem walk_empty {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {PD : D → Prop} (hd : Codec.Stream.LawfulOn PD dc)
    {s : Log.Sealer} {recordMax budget : Nat} {read : Nat → Nat → Id ByteArray} {endOff start : Nat}
    (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) :
    ∀ (fuel off : Nat) (c : D) (acc a : Acc), (acc.events = #[] → acc.full = false ∧ acc.bytes = 0) →
      walk E dc s recordMax budget read endOff start fuel off c acc = .ok a → a.events = #[] →
      a.full = false ∧ a.bytes = 0 ∧ a.steps ≤ max start acc.steps := by
  intro fuel
  induction fuel with
  | zero =>
    intro off c acc a hacc h he
    simp only [walk, pure] at h
    cases h
    exact ⟨(hacc he).1, (hacc he).2, Nat.le_max_right _ _⟩
  | succ fuel ih =>
    intro off c acc a hacc h he
    simp only [walk, bind, pure] at h
    split at h
    · cases h
      exact ⟨(hacc he).1, (hacc he).2, Nat.le_max_right _ _⟩
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
        · rename_i ts _ hdec
          have hs := decode_stepEvent_le hd hdec
          have hge := walk_events_ge _ _ _ _ _ h
          have he1 : (walkTurnsAt E budget start c acc.steps ts acc).1.events = #[] := by
            rw [he] at hge
            exact Array.eq_empty_of_size_eq_zero (Nat.le_zero.mp hge)
          obtain ⟨hf1, hb1, hk1⟩ := walkTurnsAt_empty E hB start c ts acc hs hacc he1
          obtain ⟨hf, hb, hk⟩ := ih _ _ _ _ (fun _ => ⟨hf1, hb1⟩) h he
          exact ⟨hf, hb, by omega⟩

/-- **The first record past `start` that `walk` reads, the page serves from**: from an empty page
whose count is at or below `start`, a verified frame before the durable end that decodes to steps
reaching past `start` leaves the page holding at least one event. -/
theorem walk_serves {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {PD : D → Prop} (hd : Codec.Stream.LawfulOn PD dc)
    {s : Log.Sealer} {recordMax budget : Nat} {read : Nat → Nat → Id ByteArray} {endOff start : Nat}
    (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget) {fuel off : Nat} {c : D} {acc a : Acc}
    {r : ByteArray} {ts : List (Kernel.Step D × D)}
    (hev : acc.events = #[]) (hb : acc.bytes = 0) (hf : acc.full = false) (hoff : off < endOff)
    (hr : frameOf s recordMax read off = some r) (hdec : (Record.codec dc).decode r = .ok ts)
    (hst : acc.steps ≤ start) (hpast : start < acc.steps + ts.length)
    (h : walk E dc s recordMax budget read endOff start (fuel + 1) off c acc = .ok a) :
    0 < a.events.size := by
  have hne : ts ≠ [] := by rintro rfl; simp at hpast; omega
  have hw : walk E dc s recordMax budget read endOff start (fuel + 1) off c acc =
      walk E dc s recordMax budget read endOff start fuel (off + frameSize r)
        (walkTurnsAt E budget start c acc.steps ts acc).2.1 (walkTurnsAt E budget start c acc.steps ts acc).1 := by
    simp only [walk, bind, pure, hf, Bool.false_or, decide_eq_true_eq, if_neg (Nat.not_le.mpr hoff)]
    show (match frameOf s recordMax read off with | _ => _) = _
    rw [hr]
    obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [hdec]
  rw [hw] at h
  exact Nat.lt_of_lt_of_le
    (walkTurnsAt_serves E hB start c acc.steps ts acc (decode_stepEvent_le hd hdec) hev hb hf hst hpast)
    (walk_events_ge _ _ _ _ _ h)

/-- **The walk-level tooth**: at `eventBytesMax + 4`, a first record past `start` whose first event
is of the codec's full size leaves the page `walk` returns `full` and EMPTY. -/
theorem walk_one_short {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {s : Log.Sealer} {recordMax : Nat} {read : Nat → Nat → Id ByteArray} {endOff start : Nat}
    {fuel off : Nat} {c : D} {acc : Acc} {r : ByteArray} {t : Kernel.Step D} {root : D}
    {rest : List (Kernel.Step D × D)}
    (hev : acc.events = #[]) (hb : acc.bytes = 0) (hf : acc.full = false) (hoff : off < endOff)
    (hr : frameOf s recordMax read off = some r) (hdec : (Record.codec dc).decode r = .ok ((t, root) :: rest))
    (hx : (stepEvent t).size = Kernel.Bounds.eventBytesMax + 1) (hst : start < acc.steps + 1) :
    ∃ a, walk E dc s recordMax (Kernel.Bounds.eventBytesMax + 4) read endOff start (fuel + 1) off c acc = .ok a ∧
      a.full = true ∧ a.events = #[] := by
  obtain ⟨hfull, hempty⟩ := walkTurnsAt_one_short E start c acc.steps t root rest acc hev hb hf hx hst
  refine ⟨_, ?_, hfull, hempty⟩
  simp only [walk, bind, pure, hf, Bool.false_or, decide_eq_true_eq, if_neg (Nat.not_le.mpr hoff)]
  show (match frameOf s recordMax read off with | _ => _) = _
  rw [hr]
  simp only [hdec]
  exact walk_full _ _ _ _ hfull

/-- **A page `build` returns empty was never stopped for room**: with the digest codec lawful and a
budget of `eventBytesMax + 5` (`budget_fits_event` for the deployed one), an empty page is not
`full` and holds no bytes. The tooth is `walk_one_short`. -/
theorem build_empty {D : Type} [Ord D] [DecidableEq D] {E : Kernel.Env D} {dc : Codec.Stream D}
    {PD : D → Prop} (hd : Codec.Stream.LawfulOn PD dc)
    {digestOf : ByteArray → Option D} {s : Log.Sealer} {recordMax budget : Nat}
    {read : Nat → Nat → Id ByteArray} {get : Nat → Id (Except Fault Entry)} {count endOff : Nat}
    {now : Nat × ByteArray} {start : Nat} {a : Acc} (hB : Kernel.Bounds.eventBytesMax + 5 ≤ budget)
    (h : build E dc digestOf s recordMax budget read get count endOff now start = .ok a)
    (he : a.events = #[]) : a.full = false ∧ a.bytes = 0 ∧ a.steps ≤ start := by
  rcases build_located h with ⟨hn, rfl⟩ | ⟨k, e, c, _, _, hle, _, hw⟩
  · exact ⟨rfl, rfl, hn⟩
  · obtain ⟨hf, hb, hk⟩ := walk_empty hd hB _ _ _ _ _ (fun _ => ⟨rfl, rfl⟩) hw he
    exact ⟨hf, hb, by simp only at hk; omega⟩

/-- **A page from before the log is refused by name** (HOST-61): with no index under a World past
`start`, `build` refuses `beforeLog start now.1`. -/
theorem build_beforeLog_none {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) (dc : Codec.Stream D)
    (digestOf : ByteArray → Option D) (s : Log.Sealer) (recordMax budget : Nat)
    (read : Nat → Nat → Id ByteArray) (get : Nat → Id (Except Fault Entry)) (endOff : Nat)
    (now : Nat × ByteArray) (start : Nat) (hs : start < now.1) :
    build E dc digestOf s recordMax budget read get 0 endOff now start = .error (.beforeLog start now.1) := by
  simp only [build, pure, if_neg (Nat.not_le.mpr hs), ↓reduceIte]
  rfl

/-- **A page from before the log is refused by name** (HOST-61): when the entry `locate` returns
lies past `start` (entry 0, the log beginning after it), `build` refuses `beforeLog start e.steps`
and walks nothing. -/
theorem build_beforeLog {D : Type} [Ord D] [DecidableEq D] (E : Kernel.Env D) (dc : Codec.Stream D)
    (digestOf : ByteArray → Option D) (s : Log.Sealer) (recordMax budget : Nat)
    (read : Nat → Nat → Id ByteArray) (get : Nat → Id (Except Fault Entry)) (count endOff : Nat)
    (now : Nat × ByteArray) (start k : Nat) (e : Entry) (hs : start < now.1) (hc : count ≠ 0)
    (hl : locate get count start = .ok (k, e)) (he : start < e.steps) :
    build E dc digestOf s recordMax budget read get count endOff now start = .error (.beforeLog start e.steps) := by
  simp only [build, bind, pure, if_neg (Nat.not_le.mpr hs), if_neg hc]
  rw [show (locate get count start : Id _) = .ok (k, e) from hl]
  simp only [if_pos he]

end Nanodregg.Host.Page

namespace Nanodregg.Host.Record

open Nanodregg.Kernel Nanodregg.Codec

variable {D : Type}

/-- `encode` writes the codec's bytes of exactly the pairs it was given, and only for at least one
and at most `recordTurnsMax` of them (HOST-49: an empty batch is no record). -/
theorem encode_eq_some {dc : Stream D} {staged : Array (Step D × D)} {b : ByteArray} :
    encode dc staged = some b ↔
      0 < staged.size ∧ staged.size ≤ recordTurnsMax ∧ b = (codec dc).bytes staged.toList := by
  unfold encode
  split
  · rename_i hs
    exact ⟨fun h => ⟨hs.1, hs.2, (Option.some.inj h).symm⟩, fun ⟨_, _, hb⟩ => hb ▸ rfl⟩
  · rename_i hs
    exact ⟨fun h => (by cases h), fun ⟨h0, h, _⟩ => absurd ⟨h0, h⟩ hs⟩

/-- **The empty batch is no record** (HOST-49): `encode` refuses it, the record the reader refuses
`empty`. -/
theorem encode_empty {dc : Stream D} : encode dc (#[] : Array (Step D × D)) = none := by
  unfold encode
  rw [if_neg (by simp)]

/-- **The tooth**: more than `recordTurnsMax` pairs are refused (`none`), never encoded; the append
path names it `recordTooLarge` and writes nothing. -/
theorem encode_none {dc : Stream D} {staged : Array (Step D × D)} (h : recordTurnsMax < staged.size) :
    encode dc staged = none := by
  unfold encode
  rw [if_neg (by omega)]

/-- **A writer never writes a record its own reader refuses**: a record `encode` returns, of pairs
that each fit the codec (`Step.Fits`, and the roots digest), decodes back to exactly those pairs. -/
theorem encode_decode {PD : D → Prop} {dc : Stream D} (hd : Stream.LawfulOn PD dc)
    {staged : Array (Step D × D)} {b : ByteArray} (h : encode dc staged = some b)
    (hf : ∀ p ∈ staged.toList, Kernel.Step.Fits PD p.1 ∧ PD p.2) :
    (codec dc).decode b = .ok staged.toList := by
  obtain ⟨_, hs, rfl⟩ := encode_eq_some.mp h
  exact (Codec.Kernel.batch_lawfulOn hd recordTurnsMax (by decide)).decode_bytes
    ⟨by simpa using hs, hf⟩

/-- The reopen's step over a record `encode` returned is the rooted run of its very pairs: it is
never refused `undecodable`. -/
theorem step_encode [Ord D] [DecidableEq D] {F : Type} {PD : D → Prop} {dc : Stream D} (hd : Stream.LawfulOn PD dc)
    (admit : World D → Step D → Except F (World D)) (root : World D → D) (w : World D)
    {staged : Array (Step D × D)} {b : ByteArray} (h : encode dc staged = some b)
    (hf : ∀ p ∈ staged.toList, Kernel.Step.Fits PD p.1 ∧ PD p.2) :
    step dc admit root w b = runRooted admit root 0 w staged.toList := by
  obtain ⟨hpos, _, _⟩ := encode_eq_some.mp h
  unfold step stepTurns
  rw [encode_decode hd h hf]
  have hne : staged.toList ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [Array.length_toList, List.length_nil] at this
    omega
  generalize staged.toList = l at hne ⊢
  cases l with
  | nil => exact absurd rfl hne
  | cons p ps => dsimp only; cases runRooted admit root 0 w (p :: ps) <;> rfl

/-- **The tooth of `empty`** (HOST-49): the record of no steps, the codec's own bytes of `[]`, is
refused `empty` by the reopen's step, never folded as a record that advances nothing. -/
theorem step_empty [Ord D] [DecidableEq D] {F : Type} {PD : D → Prop} {dc : Stream D} (hd : Stream.LawfulOn PD dc)
    (admit : World D → Step D → Except F (World D)) (root : World D → D) (w : World D) :
    step dc admit root w ((codec dc).bytes []) = .error .empty := by
  unfold step stepTurns codec
  rw [(Codec.Kernel.batch_lawfulOn hd recordTurnsMax (by decide)).decode_bytes ⟨by simp, by simp⟩]
  rfl

end Nanodregg.Host.Record

