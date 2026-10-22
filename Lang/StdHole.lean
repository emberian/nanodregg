/- A guarded hole: retained candidates, withdrawable facts and blocker reasons.
Acceptance dispatches the selected value as an ordinary activity. -/
import Lang.HoleSyntax

namespace Nanodregg.Lang.Std
open HoleSyntax

def holeState : Ty := .record [("accepted", .bool), ("acceptor", .digest),
  ("cap", .nat), ("chooser", .digest), ("closes", .nat), ("selected", optTy .digest)]

def holeSupport : Ty := .record [("cell", .digest), ("pin", .digest)]

def holeStatus : Ty := .sum [("conflict", .bytes), ("pruned", .bytes),
  ("suspended", .bytes), ("verified", .record [])]

def holeCandidate (V : Ty) : Ty := .record [
  ("blocker", optTy holeSupport), ("by", .digest), ("reason", .bytes),
  ("s0", optTy holeSupport), ("s1", optTy holeSupport), ("status", holeStatus), ("value", V)]

def holeCandidates (V : Ty) : RelDecl :=
  ⟨[("cand", .digest)], holeCandidate V, 64, none, 0, false, some "proposed"⟩

def holeFacts : RelDecl := ⟨[("cell", .digest)],
  .record [("by", .digest), ("pin", .digest)], 64, none, 0, true, some "posted"⟩

/-- A read of at most three fact rows: two positive supports and one blocker, each with its cell's
liveness in the caller's pinned view (E1: `facts` is keyed by `cell : digest`, so the read is a live
read). Matching is by cell identity, never by the order in which the pins arrived. -/
def holeFactsView : Ty := readsTy [("facts", holeFacts)] [("facts", ⟨3, none, true⟩)]

/-- Internal judgment preserves each refusal name until it is rendered either
as a retained row status or a method refusal. -/
def holeVerdict : Ty := .sum [
  ("conflict", .record []), ("pruned", .record []),
  ("support0Dead", .record []), ("support0Moved", .record []), ("support0Withdrawn", .record []),
  ("support1Dead", .record []), ("support1Moved", .record []), ("support1Withdrawn", .record []),
  ("verified", .record [])]

/-- One point's observation: absent 0, same token at a live cell 1, moved version 2, same token at
a cell that is not live (revoked, retired, never existed: C1) 3. -/
def holeProbePoint : Term :=
  (hl "s" holeSupport (hl "point" (livePointTy holeFacts)
    (hf (hv "point") [
      ("none", "_", hc (.nat 0)),
      ("some", "p", ht (hp .deq (hg (hg (hv "p") "key") "cell") (hg (hv "s") "cell"))
        (hf (hg (hv "p") "val") [
          ("none", "_", hc (.nat 0)),
          ("some", "f", ht (hp .deq (hg (hv "f") "pin") (hg (hv "s") "pin"))
            (ht (hg (hv "p") "live") (hc (.nat 1)) (hc (.nat 3))) (hc (.nat 2)))])
        (hc (.nat 0)))]))) []

/-- Bounded lookup by identity. Bind the probe once; its syntax is not copied
into every continuation branch. Real row views have at most one point per key. -/
def holeSupportProbe : Term :=
  let pointTy := Ty.fn holeSupport (.fn (livePointTy holeFacts) .nat)
  let probe (i : Label) := ha (hv "probe") [hv "s", hg (hg (hv "rows") "facts") i]
  let anyEq (n : Nat) := ht (hp .eq (hv "p0") (hc (.nat n))) (hb true)
    (ht (hp .eq (hv "p1") (hc (.nat n))) (hb true) (hp .eq (hv "p2") (hc (.nat n))))
  (hl "s" holeSupport (hl "rows" holeFactsView
    (hlet "probe" pointTy (hc holeProbePoint)
      (hlet "p0" .nat (probe "p0") (hlet "p1" .nat (probe "p1")
        (hlet "p2" .nat (probe "p2")
          (ht (anyEq 1) (hc (.nat 1)) (ht (anyEq 3) (hc (.nat 3))
            (ht (anyEq 2) (hc (.nat 2)) (hc (.nat 0))))))))))) []

/-- Presence is independent of liveness: an observed absent row is covered,
but an omitted point is not. Keys are rows under self, never cell pins. -/
def holePointCovered : Term :=
  (hl "s" holeSupport (hl "point" (livePointTy holeFacts)
    (hf (hv "point") [
      ("none", "_", hb false),
      ("some", "p", hp .deq (hg (hg (hv "p") "key") "cell") (hg (hv "s") "cell"))]))) []

/-- Complete observation of one declared support key in the bounded self view. -/
def holeSupportCovered : Term :=
  let P := Ty.fn holeSupport (.fn (livePointTy holeFacts) .bool)
  let probe (i : Label) := ha (hv "present") [hv "s", hg (hg (hv "rows") "facts") i]
  (hl "s" holeSupport (hl "rows" holeFactsView
    (hlet "present" P (hc holePointCovered)
      (ht (probe "p0") (hb true) (ht (probe "p1") (hb true) (probe "p2")))))) []

/-- The emitted complete-observation adapter's finite collector. All declared
supports and blockers must be observed before any verdict, even a conflict.
Missing observations refuse by role; observed absence still reaches rejudge. -/
def holeCoverageCheck : Term :=
  (hl "s0" .bool (hl "s1" .bool (hl "blocker" .bool
    (ht (hv "s0")
      (ht (hv "s1")
        (ht (hv "blocker") (hb true) (hc (.refuse .bool "pruned".toUTF8)))
        (hc (.refuse .bool "support1 withdrawn".toUTF8)))
      (hc (.refuse .bool "support0 withdrawn".toUTF8)))))) []

/-- Coverage expressions use the candidate's declared keys, not a caller's
claimed read set. Missing optional dependencies need no observation. -/
def holeCoverageTerms : List Term :=
  let covered (name : Label) := hf (hg (hv "c") name)
    [("none", "_", hb true),
     ("some", "s", ha (hv "covered") [hv "s", hv "rows"])]
  (["s0", "s1", "blocker"].map covered).map (· ["covered", "rows", "c", "state"])

def holeVerdictLabel (allowed blocked : Bool) (s0 s1 : Nat) : Label :=
  if !allowed then "conflict" else if blocked then "pruned"
  else if s0 != 1 then
    (if s0 = 2 then "support0Moved" else if s0 = 3 then "support0Dead" else "support0Withdrawn")
  else if s1 != 1 then
    (if s1 = 2 then "support1Moved" else if s1 = 3 then "support1Dead" else "support1Withdrawn")
  else "verified"

/-- The fixed judgment truth table, as executable core code. -/
def holeDecision : Term :=
  let verdict (l : Label) := hi holeVerdict l hn
  (hl "allowed" .bool (hl "blocked" .bool (hl "s0" .nat (hl "s1" .nat
    (ht (hv "allowed")
      (ht (hv "blocked") (verdict "pruned")
        (ht (hp .eq (hv "s0") (hc (.nat 1)))
          (ht (hp .eq (hv "s1") (hc (.nat 1))) (verdict "verified")
            (ht (hp .eq (hv "s1") (hc (.nat 2)))
              (verdict "support1Moved")
              (ht (hp .eq (hv "s1") (hc (.nat 3))) (verdict "support1Dead") (verdict "support1Withdrawn"))))
          (ht (hp .eq (hv "s0") (hc (.nat 2)))
            (verdict "support0Moved")
            (ht (hp .eq (hv "s0") (hc (.nat 3))) (verdict "support0Dead") (verdict "support0Withdrawn")))))
      (verdict "conflict")))))) []

/-- Observation expressions in scope probe, rows, candidate, state. Each term
reads the actual clause or a concrete optional support from the pinned view. -/
def holeObservationTerms (clause : Term) : List Term :=
  let probe (s : H) := ha (hv "probe") [s, hv "rows"]
  let support (name : Label) := hf (hg (hv "c") name)
    [("none", "_", hc (.nat 1)), ("some", "s", probe (hv "s"))]
  let blocked := hf (hg (hv "c") "blocker") [
    ("none", "_", hb false),
    ("some", "s", hp .eq (probe (hv "s")) (hc (.nat 1)))]
  ([ha (hc clause) [hv "state", hg (hv "c") "value"],
    blocked, support "s0", support "s1"] : List H).map (· ["probe", "rows", "c", "state"])

/-- The state clause, blocker and supports are recomputed from the pinned view.
The candidate's recorded status is never trusted. -/
def holeJudge (V : Ty) (clause : Term) : Term :=
  let probeTy := Ty.fn holeSupport (.fn holeFactsView .nat)
  .lam holeState (.lam (holeCandidate V) (.lam holeFactsView
    (.app (.lam probeTy (activityApply holeDecision (holeObservationTerms clause)))
      holeSupportProbe)))

/-- The receive-path judge first collects the complete declared observation.
This wrapper is shared by propose, fill, select, accept, prune and rejudge. -/
def holeCheckedJudge (V : Ty) (clause : Term) : Term :=
  let coveredTy := Ty.fn holeSupport (.fn holeFactsView .bool)
  .lam holeState (.lam (holeCandidate V) (.lam holeFactsView
    (.app (.lam coveredTy
      (.app (.lam .bool (activityApply (holeJudge V clause) [.var 4, .var 3, .var 2]))
        (activityApply holeCoverageCheck holeCoverageTerms)))
      holeSupportCovered)))

/-- Render judgment into the row while keeping the pruning reason separately
on the candidate even after its blocker is withdrawn. -/
def holeStatusOf : Term :=
  (hl "reason" .bytes (hl "verdict" holeVerdict
    (hf (hv "verdict") [
      ("conflict", "_", hi holeStatus "conflict" (hs "clause")),
      ("pruned", "_", hi holeStatus "pruned" (hv "reason")),
      ("support0Dead", "_", hi holeStatus "suspended" (hs "support0 dead")),
      ("support0Moved", "_", hi holeStatus "suspended" (hs "support0 moved")),
      ("support0Withdrawn", "_", hi holeStatus "suspended" (hs "support0 withdrawn")),
      ("support1Dead", "_", hi holeStatus "suspended" (hs "support1 dead")),
      ("support1Moved", "_", hi holeStatus "suspended" (hs "support1 moved")),
      ("support1Withdrawn", "_", hi holeStatus "suspended" (hs "support1 withdrawn")),
      ("verified", "_", hi holeStatus "verified" hn)]))) []


/-- The admission gate used by select, fill and accept. Rejudge does not call it. -/
def holeVerdictCheck : Term :=
  (hl "verdict" holeVerdict (hf (hv "verdict") [
    ("conflict", "_", hc (.refuse .bool "conflict".toUTF8)),
    ("pruned", "_", hc (.refuse .bool "pruned".toUTF8)),
    ("support0Dead", "_", hc (.refuse .bool "support0 dead".toUTF8)),
    ("support0Moved", "_", hc (.refuse .bool "support0 moved".toUTF8)),
    ("support0Withdrawn", "_", hc (.refuse .bool "support0 withdrawn".toUTF8)),
    ("support1Dead", "_", hc (.refuse .bool "support1 dead".toUTF8)),
    ("support1Moved", "_", hc (.refuse .bool "support1 moved".toUTF8)),
    ("support1Withdrawn", "_", hc (.refuse .bool "support1 withdrawn".toUTF8)),
    ("verified", "_", hb true)])) []

private def hadmit (_T : Ty) (v success : H) : H :=
  hlet "_admitted" .bool (ha (hc holeVerdictCheck) [v]) success

private def hcheck (_T : Ty) (c : H) (why : String) (rest : H) : H :=
  hlet "_checked" .bool (ht c (hb true) (hc (.refuse .bool why.toUTF8))) rest

private def hunwrap (T : Ty) (value : H) (why : String) : H :=
  hf value [("none", "_", hc (.refuse T why.toUTF8)), ("some", "_value", hv "_value")]

/-- Poster-only fact edits. An upsert cannot transfer ownership. -/
def holePosted : Term :=
  let yours (x : H) := hp .deq (hg x "by") (hg (hv "req") "agent")
  let present (rest : H) := hf (hg (hv "input") "old") [
    ("none", "_", hc (refusedT "unknown")), ("some", "old", rest)]
  (hl "state" holeState (hl "req" reqTy (hl "input" (guardInTy holeFacts)
    (hf (hg (hv "input") "edit") [
      ("insert", "x", hguard (yours (hg (hv "x") "val")) "notYours" (hc okT)),
      ("retract", "x", present (hguard (yours (hv "old")) "notYours" (hc okT))),
      ("upsert", "x", present (hguard (yours (hv "old")) "notYours"
        (hguard (yours (hg (hv "x") "val")) "notYours" (hc okT))))])))) []

/-- Guards can recheck the state/value clause and row immutability. Fact
liveness is read by the methods and rechecked on every select/fill/accept;
the kernel pins those reads. A guard cannot read another relation. -/
def holeProposed (V : Ty) (clause : Term) : Term :=
  let nv := hg (hv "x") "val"
  let chooser := hp .deq (hg (hv "req") "agent") (hg (hv "state") "chooser")
  let agrees := hf (hg nv "status") [
    ("conflict", "_", hguard
      (ht (ha (hc clause) [hv "state", hg nv "value"]) (hb false) (hb true)) "status" (hc okT)),
    ("pruned", "_", hguard (ha (hc clause) [hv "state", hg nv "value"]) "status" (hc okT)),
    ("suspended", "_", hguard (ha (hc clause) [hv "state", hg nv "value"]) "status" (hc okT)),
    ("verified", "_", hguard (ha (hc clause) [hv "state", hg nv "value"]) "status" (hc okT))]
  let same (f : Label) (T : Ty) (rest : H) :=
    hguard (he T (hg nv f) (hg (hv "old") f)) f rest
  let pruning := ht
    (he (.record [("blocker", optTy holeSupport), ("reason", .bytes)])
      (hr [("blocker", hg nv "blocker"), ("reason", hg nv "reason")])
      (hr [("blocker", hg (hv "old") "blocker"), ("reason", hg (hv "old") "reason")]))
    agrees (hguard chooser "notChooser" agrees)
  (hl "state" holeState (hl "req" reqTy (hl "input" (guardInTy (holeCandidates V))
    (hf (hg (hv "input") "edit") [
      ("insert", "x", hguard (hp .deq (hg nv "by") (hg (hv "req") "agent")) "notYours"
        (hf (hg nv "blocker") [
          ("none", "_", hf (hg nv "status") [
            ("conflict", "_", agrees), ("pruned", "_", hc (refusedT "prunedAtBirth")),
            ("suspended", "_", agrees), ("verified", "_", agrees)]),
          ("some", "_", hc (refusedT "prunedAtBirth"))])),
      ("upsert", "x", hf (hg (hv "input") "old") [
        ("none", "_", hc (refusedT "unknown")),
        ("some", "old", same "value" V (same "by" .digest
          (same "s0" (optTy holeSupport) (same "s1" (optTy holeSupport) pruning))))])])))) []

/-- The hole's fixed policy; acceptance starts the chosen value's activity.
Only the acceptor can acknowledge that dispatch via resume_fill. -/
def holePlan (V : Ty) : ActivityPlan := {
  name := "fill", captured := V, response := .record [],
  precondition := (hl "s" holeState (hl "v" V (hl "q" reqTy (hb true)))) [],
  start := (hl "s" holeState (hl "v" V (hl "q" reqTy (hu (hv "s") [("accepted", hb true)])))) [],
  resume := (hl "s" holeState (hl "v" V (hl "response" (.record []) (hl "q" reqTy (hv "s"))))) [] }

def holeResumer : Term :=
  (hl "state" holeState (hl "req" reqTy
    (hp .deq (hg (hv "req") "agent") (hg (hv "state") "acceptor")))) []


/-- Generate one hole object. Selection is still revisable; acceptance is the
dispatch boundary and starts the immutable captured-value activity. The generic
start_fill is not exported: only accept may dispatch a selected candidate. -/
def holePackage (V : Ty) (clause : Term) (extraRels : List (Label × RelDecl) := []) : Package := Id.run do
  let p := holePlan V
  let base := activityPackage holeState "pending" "fills" 64 1024 holeResumer [p]
    ([("candidates", holeCandidates V), ("facts", holeFacts)] ++ extraRels)
  let rels := base.rels
  let E := editTy rels
  let candArg := Ty.record [("cand", .digest)]
  let proposal := Ty.record [("cand", .digest), ("s0", optTy holeSupport),
    ("s1", optTy holeSupport), ("value", V)]
  let pruneArg := Ty.record [("blocker", holeSupport), ("cand", .digest), ("why", .bytes)]
  let factArg := Ty.record [("cell", .digest), ("pin", .digest)]
  let readFacts := readsTy rels [("facts", ⟨3, none, true⟩)]
  let readBoth := readsTy rels [("candidates", ⟨1, none, false⟩), ("facts", ⟨3, none, true⟩)]
  let facts := hr [("facts", hg (hv "rows") "facts")]
  let judge (c : H) := ha (hv "holeJudge") [hv "state", c, facts]
  let status (c : H) := ha (hc holeStatusOf) [hg c "reason", judge c]
  let edit (name : Label) (d : RelDecl) (op : Label) (key val : H) : H :=
    fun sc => activityEdit rels name d op (key sc) (val sc)
  let done (state : H) (edits : List H) : H :=
    fun sc => activityResult rels (state sc) (edits.map (· sc))
  let key := hr [("cand", hg (hv "arg") "cand")]
  let chosen := hu (hv "state") [("selected", hsome .digest (hg (hv "arg") "cand"))]
  let canChoose (T : Ty) (rest : H) := hcheck T
    (hp .deq (hg (hv "req") "agent") (hg (hv "state") "chooser")) "notChooser"
    (hcheck T (ht (hg (hv "state") "accepted") (hb false) (hb true)) "accepted" rest)
  let readCandidate (T : Ty) (id : H) (rest : H) :=
    hlet "point" (.record [("key", keyTy (holeCandidates V)), ("val", optTy (holeCandidate V))])
      (hunwrap (.record [("key", keyTy (holeCandidates V)), ("val", optTy (holeCandidate V))])
        (hg (hg (hv "rows") "candidates") "p0") "unknown")
      (hlet "c" (holeCandidate V) (hunwrap (holeCandidate V) (hg (hv "point") "val") "unknown")
        (hcheck T (hp .deq (hg (hg (hv "point") "key") "cand") id) "unknown" rest))
  let fresh := hr [("blocker", hnone holeSupport), ("by", hg (hv "req") "agent"),
    ("reason", hs ""), ("s0", hg (hv "arg") "s0"), ("s1", hg (hv "arg") "s1"),
    ("status", hi holeStatus "verified" hn), ("value", hg (hv "arg") "value")]
  let insert := edit "candidates" (holeCandidates V) "insert" key
    (hu fresh [("status", status fresh)])
  let update (c : H) := edit "candidates" (holeCandidates V) "upsert"
    (hg (hv "point") "key") (hu c [("status", status c)])
  let R1 := resultTy holeState [] E 1
  let R2 := resultTy holeState [] E 2
  let proposalBody := hcheck R1
    (hp .le (hg (hv "req") "validUntil") (hg (hv "state") "closes")) "closed"
    (done (hv "state") [insert])
  let fillBody := canChoose R1 (hcheck R1
    (hp .le (hg (hv "req") "validUntil") (hg (hv "state") "closes")) "closed"
    (hadmit R1 (judge fresh) (done chosen [insert])))
  let selectBody := canChoose R1 (readCandidate R1 (hg (hv "arg") "cand")
    (hadmit R1 (judge (hv "c")) (done chosen [update (hv "c")])))
  let rejudgeBody := readCandidate R1 (hg (hv "arg") "cand")
    (done (hv "state") [update (hv "c")])
  let pruned := hu (hv "c") [
    ("blocker", hsome holeSupport (hg (hv "arg") "blocker")), ("reason", hg (hv "arg") "why")]
  let pruneBody := canChoose R1 (readCandidate R1 (hg (hv "arg") "cand")
    (done (hv "state") [update pruned]))
  let cd := activityCursor [p] 64 "pending_queued"
  let ld := activityLog [p] 1024 "fills_waiting"
  let acceptBody := hcheck R2
    (hp .deq (hg (hv "req") "agent") (hg (hv "state") "acceptor")) "notAcceptor"
    (hcheck R2 (ht (hg (hv "state") "accepted") (hb false) (hb true)) "accepted"
      (hlet "selected" .digest (hunwrap .digest (hg (hv "state") "selected") "unselected")
        (readCandidate R2 (hv "selected")
          (hadmit R2 (judge (hv "c"))
            (ha (hc (activityStartMethod holeState rels "pending" "fills" cd ld [p] p))
              [hn, hv "state", hg (hv "c") "value", hv "req"])))))
  let factKey := hr [("cell", hg (hv "arg") "cell")]
  let factVal := hr [("by", hg (hv "req") "agent"), ("pin", hg (hv "arg") "pin")]
  let method (A R : Ty) (b : H) : Term :=
    (hl "rows" R (hl "state" holeState (hl "arg" A (hl "req" reqTy b)))) ["holeJudge"]
  let methods : List (Label × Ty × Ty × Nat × H) := [
    ("accept", .record [], readBoth, 2, acceptBody),
    ("fill", proposal, readFacts, 1, fillBody),
    ("post", factArg, .record [], 1, done (hv "state") [edit "facts" holeFacts "insert" factKey factVal]),
    ("propose", proposal, readFacts, 1, proposalBody),
    ("prune", pruneArg, readBoth, 1, pruneBody),
    ("rejudge", candArg, readBoth, 1, rejudgeBody),
    ("repin", factArg, .record [], 1, done (hv "state") [edit "facts" holeFacts "upsert" factKey factVal]),
    ("select", candArg, readBoth, 1, selectBody),
    ("unpost", .record [("cell", .digest)], .record [], 1,
      done (hv "state") [edit "facts" holeFacts "retract" factKey hn])]
  let frozen := [("acceptor", Ty.digest), ("cap", .nat), ("chooser", .digest), ("closes", .nat)]
  let shape : H := fun sc => allOf (frozen.map fun (f, T) =>
    (eqData T ((hg (hv "old") f) sc) ((hg (hv "new") f) sc), f))
  let law := (hl "old" holeState (hl "new" holeState (hl "req" reqTy shape))) []
  let extras : List (Label × Ty × Term) :=
    [("posted", guardTy holeState holeFacts, holePosted),
      ("proposed", guardTy holeState (holeCandidates V), holeProposed V clause),
      ("shape", lawTy holeState, law)] ++
    methods.map (fun (n, A, R, es, b) => (n, methodTy holeState A [] R E es, method A R b))
  let .record oldTypes := base.iface | return base
  let .record oldTerms := base.body | return base
  let types := (oldTypes.filter (·.1 != "start_fill")) ++ extras.map fun (n, T, _) => (n, T)
  let terms := (oldTerms.filter (·.1 != "start_fill")) ++ extras.map fun (n, _, t) => (n, t)
  return { base with
    iface := .record (Row.sort types), body := .app (.lam (.fn holeState (.fn (holeCandidate V) (.fn holeFactsView holeVerdict)))
      (.record (Row.sort terms))) (holeCheckedJudge V clause),
    methods := (Row.sort (((base.methods.filter (· != "start_fill")) ++
      methods.map (·.1)).map (·, ()))).map (·.1), laws := ["shape"] }


inductive HoleRefusal
  | check (why : CheckError)
  | layout
  | fieldTooLarge (name : Label)
  | imports
  | rootTooLarge

def HoleRefusal.name : HoleRefusal → String
  | .check e => e.text
  | .layout => "holeLayout"
  | .fieldTooLarge n => "holeFieldTooLarge " ++ n
  | .imports => "holeImports"
  | .rootTooLarge => "holeRootTooLarge"

/-- Ordinary ROM packages plus an unlinked root layout. link supplies the
installed library IDs; only its checked result is installable. -/
structure HoleBundle where
  libraries : List Package
  layout : Package

def HoleBundle.link (b : HoleBundle) (ids : List ByteArray) : Except HoleRefusal Package := do
  if ids.length != b.libraries.length then throw .imports
  let p := { b.layout with imports := ids }
  match p.checkWith (b.libraries.map (·.iface)) with
  | .error e => throw (.check e)
  | .ok () => pure ()
  let some bytes := Wire.encodePackage p | throw .rootTooLarge
  if bytes.size > Bounds.bytesMax then throw .rootTooLarge
  pure p

/-- Emit a bounded import bundle. Helpers are ordinary checked ROMs; the root
contains only field selections from them. No bound or wire format changes. -/
def hole (V : Ty) (clause : Term) (extraRels : List (Label × RelDecl) := []) : Except HoleRefusal HoleBundle := do
  let p := holePackage V clause extraRels
  match p.checkWith [] with
  | .error e => throw (.check e)
  | .ok () => pure ()
  let .record ts := p.iface | throw .layout
  let .app (.lam JT (.record fs)) judge := p.body | throw .layout
  let fields ← fs.mapM fun (n, t) => do
    let some T := Row.find? n ts | throw .layout
    pure (n, T, t)
  let library (group : List (Label × Ty × Term)) : Package := {
    imports := [], state := .record [],
    iface := .record (group.map fun (n, T, _) => (n, T)),
    body := .app (.lam JT (.record (group.map fun (n, _, t) => (n, t)))) judge,
    methods := [], laws := [], rels := [] }
  let fits (group : List (Label × Ty × Term)) : Bool :=
    match Wire.encodePackage (library group) with
    | none => false
    | some bytes => bytes.size ≤ Bounds.bytesMax
  let mut groups : List (List (Label × Ty × Term)) := []
  let mut current := []
  for f in fields do
    if fits (current ++ [f]) then current := current ++ [f]
    else
      if current.isEmpty || !fits [f] then throw (.fieldTooLarge f.1)
      groups := groups ++ [current]
      current := [f]
  if !current.isEmpty then groups := groups ++ [current]
  let libraries := groups.map library
  for lib in libraries do
    match lib.checkWith [] with
    | .error e => throw (.check e)
    | .ok () => pure ()
  let rootFields := groups.zipIdx.flatMap fun (group, i) =>
    group.map fun (n, _, _) => (n, Term.get (.ref i) n)
  pure ⟨libraries, { p with body := .record (Row.sort rootFields) }⟩

end Nanodregg.Lang.Std
