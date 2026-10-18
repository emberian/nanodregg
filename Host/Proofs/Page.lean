/-
# Host.Proofs.Page — a log page always has room for the next event, is never built from an entry that failed, and never holds more steps than one record

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
          { steps := e.steps, chain := e.chain } = .ok a := by
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
        { steps := e.steps, chain := e.chain } = .ok a := by
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
  simp only at hb ⊢
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
  rcases build_located h with ⟨_, rfl⟩ | ⟨k, e, c, _, _, _, hw⟩
  · show 0 ≤ recordTurnsMax; exact Nat.zero_le _
  · exact walk_events_le _ _ _ _ _ (Nat.zero_le _) hw

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

