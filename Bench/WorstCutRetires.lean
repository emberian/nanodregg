/-
# Bench.WorstCutRetires — `bench-worstcut-retires SCRATCH [--harness-control]` (PERF-6, PERF-12)

The worst cut's `retires` tail: `revoke`s, each retiring one grant (a cell tombstoned, its weight
credited). The grants are born BEFORE the base, enough for the whole tail (a revoke's frame is
sampled on the World and the count re-derived from the sealed base's tailMax until it suffices),
sealing whenever the pre-base tail is full, so the base the tail folds onto holds every grant it
retires. Bench.WorstCut builds, counts and prints.
-/
import Bench.WorstCut

namespace Nanodregg.Bench.WorstCut.Retires

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Bench.WorstCut

/-- The call of tail step `i` on `w`: the revoke of `grants[i]`. -/
def revokeCall (w : World D) (m : Who) (grants : Array D) (i : Nat) : Except String (Call D) :=
  if h : i < grants.size then let g := grants[i]; .ok (call w m [m.id, g] (.revoke g))
  else .error s!"no grant left to retire at step {i} (the base holds {grants.size})"

/-- Bear grants of `obj` to the founder (`mutate`, unparented: the founder acts as itself) until
`goal` of them exist or the tail past the newest base is full, `recordTurnsMax` per record; the
World and grants after. -/
def bearGrants (dir : System.FilePath) (keys : Keys) (m : Who) (obj : D) (goal : Nat)
    (w0 : World D) (grants0 : Array D) : IO (Except String (World D × Array D)) := do
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return .error s!"open for the grants {f.text}"
  let mut w := w0
  let mut grants := grants0
  let mut pos := wr.opening.pos
  -- a bound on the loop, never reached: one record per round
  for _ in [0:(goal - grants0.size) / recordTurnsMax + 1] do
    if grants.size ≥ goal then break
    let mut staged : Array (Step D × D) := #[]
    let mut w' := w
    let mut born : Array D := #[]
    for _ in [0:min recordTurnsMax (goal - grants.size)] do
      match admitBorn w' m [m.id] (.grant obj m.id [.mutate] none) with
      | .ok (s, w'', some g) => staged := staged.push s; w' := w''; born := born.push g
      | .ok (_, _, none) => return .error "a grant bore no cell"
      | .error e => return .error s!"grant {grants.size + born.size}: {e}"
    match ← commit wr.opening.sealed wr keys pos staged with
    | .ok (some p) => pos := p; w := w'; grants := grants ++ born
    | .ok none => break
    | .error e => return .error s!"commit {e}"
  (← wr.segment.get).sync
  return .ok (w, grants)

/-- The frame of one record of `recordTurnsMax` revokes staged on `w` (never committed): what the
tail pays per record. -/
def revokeFrame (w : World D) (m : Who) (grants : Array D) : Except String Nat := do
  let mut staged : Array (Step D × D) := #[]
  let mut w' := w
  for i in [0:recordTurnsMax] do
    let (s, w'') ← admit w' (← revokeCall w' m grants i)
    staged := staged.push s; w' := w''
  let some rec_ := Record.encode Codec.Deployed.digestCodec staged | throw "a record past its bounds"
  pure (frameSize rec_)

/-- Grants until those the newest base holds cover the tail its own tailMax allows: each round bears
toward the need (or until the pre-base tail is full), seals, and re-derives the need from that base
(a bound on the rounds, never reached). -/
def grantBase (dir : System.FilePath) (keys : Keys) (m : Who) (obj : D) (w0 : World D)
    (grants0 : Array D) : IO (Except String (World D × Array D)) := do
  let mut w := w0
  let mut grants := grants0
  let mut need := recordTurnsMax
  let mut covered := false
  for _ in [0:32] do
    if covered then break
    match ← bearGrants dir keys m obj need w grants with
    | .ok (w', gs) => w := w'; grants := gs
    | .error e => return .error e
    let sealed ← match ← sealBase dir keys with
      | .ok s => pure s
      | .error e => return .error e
    if grants.size ≥ need then
      let frame ← match revokeFrame w m grants with
        | .ok f => pure f
        | .error e => return .error s!"revoke sample: {e}"
      let need' := recordTurnsMax * (c.tailMax sealed.bytes / frame + 2)
      if grants.size ≥ need' then covered := true else need := need'
  unless covered do return .error s!"the base holds {grants.size} grants, short of the tail's need {need}"
  return .ok (w, grants)

def shape : Shape (Array D) where
  name := "retires"
  first _ _ w _ := pure (.ok (#[], w, #[]))
  beforeTail dir keys m obj w grants := grantBase dir keys m obj w grants
  step grants m _ w i := (revokeCall w m grants i).map (·, grants)
  note grants := s!", grants in the base {grants.size}"

end Nanodregg.Bench.WorstCut.Retires
