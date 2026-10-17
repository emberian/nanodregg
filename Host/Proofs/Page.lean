/-
# Host.Proofs.Page — a log page always has room for the next event, and is never built from an entry that failed

`Page.walkTurns` stops a page when the next event does not fit the budget. With the deployed
budget that can only happen after at least one event: every event fits an empty page
(`budget_fits_event`), so a page short of the tip is never empty (PROTOCOL's follow refuses an
empty page short of the tip as `badResult`).

HOST-33 (condition 2, never-served): a page meets index entries only through `entryAt`, and is
built from ONE of them, the one `locate` returns.

* `locate_got` — the entry `locate` returns is what its reader returned at that position;
* `entryAt_ok` — what `entryAt` returns from `index.log` read back at its position (its tag
  verified there: `Entry.read_sound`), and past the disk entries is the loop's own;
* `build_located` / `build_never_served` — a page that is served is the walk of the segment from
  that one entry, so no page is built from an entry whose tag failed;
* `build_badIndex` — the tooth: when the first entry a search reads does not read back, the page
  is refused `badIndex 0`, by name.

Stated in `Id` over a pure reader; `Host.Deployed.pager` runs the same `build` in `IO` over the
files.
-/
import Host.Page
import Host.Proofs.Index

namespace Nanodregg.Host.Page

theorem budget_fits_event : Kernel.Bounds.eventBytesMax + 4 ≤ budget := by decide

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
    ((now.1 ≤ start ∨ count = 0) ∧ a = ⟨#[], 0, now.1, now.2, false⟩) ∨
      ∃ k e c, locate get count start = .ok (k, e) ∧ get k = .ok e ∧ digestOf e.chain = some c ∧
        walk E dc s recordMax budget read endOff start (count - k) e.offset c
          { height := e.height, chain := e.chain } = .ok a := by
  simp only [build] at h
  split at h
  · rename_i hc
    simp only [pure] at h; cases h; exact Or.inl ⟨hc, rfl⟩
  · simp only [bind] at h
    split at h
    · simp only [pure] at h; cases h
    · rename_i k e hl
      split at h
      · simp only [pure] at h; cases h
      · rename_i c hd
        exact Or.inr ⟨k, e, c, hl, locate_got hl, hd, h⟩

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
      count endOff now start = .ok a) (hs : start < now.1) (hc : count ≠ 0) :
    ∃ k e c,
      ((k < disk ∧ Entry.bytes keys k e = rd (k * entryBytes keys) (entryBytes keys)) ∨
        (disk ≤ k ∧ mem[k - disk]? = some e)) ∧
      digestOf e.chain = some c ∧
      walk E dc s recordMax budget read endOff start (count - k) e.offset c
        { height := e.height, chain := e.chain } = .ok a := by
  rcases build_located h with ⟨hc', _⟩ | ⟨k, e, c, _, hg, hd, hw⟩
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
  rw [if_neg (by omega)]

end Nanodregg.Host.Page
