/- Activity generators: ordinary packages with continuation rows. -/
import Lang.Std

namespace Nanodregg.Lang.Std

/-! ## Activities: a cursor and an immutable captured continuation log -/

/-- A plan's code is closed core functions. Precondition and start take state,
captured argument, request; resume takes state, captured argument, response,
request. The response may be cased on by the author's resume function. -/
structure ActivityPlan where
  name : Label
  captured : Ty
  response : Ty
  precondition : Term
  start : Term
  resume : Term

inductive ActivityRefusal
  | noPlans
  | tooManyPlans
  | duplicatePlan
  | sameRelation
  | package (why : CheckError)

def ActivityRefusal.name : ActivityRefusal → String
  | .noPlans => "noPlans"
  | .tooManyPlans => "tooManyPlans"
  | .duplicatePlan => "duplicatePlan"
  | .sameRelation => "sameRelation"
  | .package why => why.text

/-- The continuation key keeps time first in the declared order, as the Bell's
queue does; its record representation is canonical by label. -/
def activityKey : List (Label × Ty) := [("notBefore", .nat), ("agent", .digest)]

def activityCaptured (plans : List ActivityPlan) : Ty :=
  .sum (Row.sort (plans.map fun p => (p.name, p.captured)))

def activityResponses (plans : List ActivityPlan) : Ty :=
  .sum (Row.sort (plans.map fun p => (p.name, p.response)))

def activityCursor (plans : List ActivityPlan) (limit : Nat) (g : Label) : RelDecl :=
  ⟨activityKey, .record [("captured", activityCaptured plans)], limit, none, 0, true, some g⟩

def activityLog (plans : List ActivityPlan) (limit : Nat) (g : Label) : RelDecl :=
  ⟨activityKey, .record [("answered", optTy (activityResponses plans)),
    ("captured", activityCaptured plans)], limit, none, 0, true, some g⟩

def activityApply (f : Term) (args : List Term) : Term := args.foldl Term.app f

/-- Compare the plan tags, without inspecting either payload. A response to one
plan cannot settle a different plan, even through another package method. -/
def activitySamePlan (plans : List ActivityPlan) (x y : Term) : Term :=
  let names := Row.sort (plans.map fun p => (p.name, ()))
  .app (.app (.lam (activityCaptured plans) (.lam (activityResponses plans)
    (.case (.var 1) (names.map fun (l, _) =>
      (l, .case (.var 1) (names.map fun (k, _) => (k, .bool (l == k)))))))) x) y

/-- Applications retain their established refusal names while sharing the same
continuation checks. Names change diagnostics, never guard predicates. -/
structure ActivityVocabulary where
  notResumer : String := "notResumer"
  unstarted : String := "unstarted"
  captured : String := "captured"

/-- Row guard for an activity log. Its old row is read by the kernel at the
edited key; capture and plan cannot change when the row is answered. -/
def activityWaiting (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term) (names : ActivityVocabulary := {}) : Term :=
  let f (i : Nat) (l : Label) := Term.get (.var i) l
  let key (i : Nat) := Term.get (f i "key") "agent"
  let val (i : Nat) (l : Label) := Term.get (f i "val") l
  .lam S (.lam reqTy (.lam (guardInTy d)
    (.case (f 0 "edit") [
      ("insert", guard (.prim .deq (key 0) (f 2 "agent")) "notYours"
        (.case (val 0 "answered") [("none", okT), ("some", refusedT "answered")])),
      ("retract", .case (f 1 "old") [
        ("none", refusedT names.unstarted),
        ("some", .case (f 0 "answered") [("none", refusedT "unanswered"), ("some", okT)])]),
      ("upsert", guard (activityApply resumer [.var 3, .var 2]) names.notResumer
        (.case (f 1 "old") [
          ("none", refusedT names.unstarted),
          ("some", .case (f 0 "answered") [
            ("none", guard (eqData (activityCaptured plans) (val 2 "captured") (f 1 "captured")) names.captured
              (.case (val 2 "answered") [
                ("none", refusedT "unanswered"),
                ("some", guard (activitySamePlan plans (val 3 "captured") (.var 0)) "plan" okT)])),
            ("some", refusedT "answered")])]))])))

/-- The cursor is insert/retract only: insertion is by the key's signer,
retraction by the resumer. No phase field is written into object state. -/
def activityQueued (S : Ty) (d : RelDecl) (resumer : Term)
    (names : ActivityVocabulary := {}) : Term :=
  .lam S (.lam reqTy (.lam (guardInTy d) (.case (.get (.var 0) "edit") [
    ("insert", guard (.prim .deq (.get (.get (.var 0) "key") "agent") (.get (.var 2) "agent")) "notYours" okT),
    ("retract", guard (activityApply resumer [.var 3, .var 2]) names.notResumer okT),
    ("upsert", refusedT "final")])))

def activityKeyTerm (agent notBefore : Term) : Term :=
  .record [("agent", agent), ("notBefore", notBefore)]

def activityEdit (rels : List (Label × RelDecl)) (name : Label) (d : RelDecl)
    (op : Label) (key : Term) (value : Term := .record []) : Term :=
  .inj (editTy rels) name (.inj (relEditTy d) op
    (.record (if op = "retract" then [("key", key)] else [("key", key), ("val", value)])))

def activityResult (rels : List (Label × RelDecl)) (state : Term) (edits : List Term) : Term :=
  resultT (.record []) state (.record ((slotLabels "e" edits.length).zip
    (edits.map fun t => someCallT (editTy rels) t)))

def activityMethod (S A R : Ty) (body : Term) : Term :=
  .lam R (.lam S (.lam A (.lam reqTy body)))

def activityResumeArg (p : ActivityPlan) : Ty :=
  .record [("agent", .digest), ("notBefore", .nat), ("response", p.response)]

/-- The generated start method, factored so its semantics can be stated without
unfolding package assembly. -/
def activityStartMethod (S : Ty) (rels : List (Label × RelDecl)) (cursor log : Label)
    (cd ld : RelDecl) (plans : List ActivityPlan) (p : ActivityPlan) : Term :=
  let E := editTy rels
  let C := activityCaptured plans
  let R := activityResponses plans
  let f (i : Nat) (l : Label) := Term.get (.var i) l
  let key (i : Nat) := activityKeyTerm (f i "agent") (f i "notBefore")
  let cap := Term.inj C p.name (.var 1)
  let startBody := Term.ite (activityApply p.precondition [.var 2, .var 1, .var 0])
    (activityResult rels (activityApply p.start [.var 2, .var 1, .var 0]) [
      activityEdit rels cursor cd "insert" (key 0) (.record [("captured", cap)]),
      activityEdit rels log ld "insert" (key 0)
        (.record [("answered", noCallT R), ("captured", cap)])])
    (.refuse (resultTy S [] E 2) "precondition".toUTF8)
  activityMethod S p.captured (.record []) startBody

/-- The two edits and response-dependent state produced by a resumption. -/
def activityResumeResult (rels : List (Label × RelDecl)) (cursor log : Label)
    (cd ld : RelDecl) (plans : List ActivityPlan) (p : ActivityPlan) : Term :=
  let R := activityResponses plans
  let f (i : Nat) (l : Label) := Term.get (.var i) l
  let key (i : Nat) := activityKeyTerm (f i "agent") (f i "notBefore")
  activityResult rels
    (activityApply p.resume [.var 5, .var 0, f 4 "response", .var 3]) [
      activityEdit rels log ld "upsert" (key 4) (.record [
        ("answered", someCallT R (.inj R p.name (f 4 "response"))),
        ("captured", f 1 "captured")]),
      activityEdit rels cursor cd "retract" (key 4)]

/-- The generated response-dependent resumption, including the keyed row read. -/
def activityResumeMethod (S : Ty) (rels : List (Label × RelDecl)) (cursor log : Label)
    (cd ld : RelDecl) (resumer : Term) (plans : List ActivityPlan) (p : ActivityPlan) : Term :=
  let E := editTy rels
  let f (i : Nat) (l : Label) := Term.get (.var i) l
  let key (i : Nat) := activityKeyTerm (f i "agent") (f i "notBefore")
  let A := activityResumeArg p
  let result := resultTy S [] E 2
  let fail (why : String) := Term.refuse result why.toUTF8
  -- Under three case binders: captured=0, old value=1, point=2,
  -- request=3, argument=4, state=5, rows=6.
  let resumeDone := activityResumeResult rels cursor log cd ld plans p
  let resumeBody := Term.ite (activityApply resumer [.var 2, .var 0])
    (.case (.get (.get (.var 3) log) "p0") [
      ("none", fail "unknown"),
      ("some", .case (f 0 "val") [
        ("none", fail "unknown"),
        ("some", .ite (eqData (keyTy ld) (f 1 "key") (key 3))
          (.case (f 0 "captured") ((Row.sort (plans.map fun q => (q.name, ()))).map fun (l, _) =>
            (l, if l = p.name then resumeDone else fail "wrongPlan")))
          (fail "key"))])])
    (fail "notResumer")
  activityMethod S A (readsTy rels [(log, ⟨1, none⟩)]) resumeBody

/-- Emit the activity as an ordinary checked package. Additional application
methods/laws can be composed with its fields; the final package is checked by
the same install checker. Limits are the relation's normal kernel bounds. -/
def activityPackage (S : Ty) (cursor log : Label) (cursorLimit logLimit : Nat)
    (resumer : Term) (plans : List ActivityPlan)
    (extraRels : List (Label × RelDecl) := [])
    (guardNames : Option (Label × Label) := none) (names : ActivityVocabulary := {}) : Package := Id.run do
  let cg := (guardNames.map (·.1)).getD (cursor ++ "_queued")
  let lg := (guardNames.map (·.2)).getD (log ++ "_waiting")
  let cd := activityCursor plans cursorLimit cg
  let ld := activityLog plans logLimit lg
  let rels := Row.sort ([(cursor, cd), (log, ld)] ++ extraRels)
  let E := editTy rels
  let reads := readsTy rels [(log, ⟨1, none⟩)]
  let empty := Ty.record []
  let f (i : Nat) (l : Label) := Term.get (.var i) l
  let key (i : Nat) := activityKeyTerm (f i "agent") (f i "notBefore")
  let mut fields : List (Label × Ty × Term) := [
    (cg, guardTy S cd, activityQueued S cd resumer names),
    (lg, guardTy S ld, activityWaiting S plans ld resumer names)]
  let mut methods : List Label := []
  for p in plans do
    let startName := "start_" ++ p.name
    let resumeName := "resume_" ++ p.name
    fields := fields ++ [
      (startName, methodTy S p.captured [] empty E 2,
        activityStartMethod S rels cursor log cd ld plans p),
      (resumeName, methodTy S (activityResumeArg p) [] reads E 2,
        activityResumeMethod S rels cursor log cd ld resumer plans p)]
    methods := methods ++ [startName, resumeName]
  let K := keyTy ld
  fields := fields ++ [("retire", methodTy S K [] empty E 1,
    activityMethod S K empty (activityResult rels (.var 2) [activityEdit rels log ld "retract" (key 1)]))]
  methods := methods ++ ["retire"]
  let sortedFields := Row.sort fields
  let pkg : Package := {
    imports := [], state := S,
    iface := .record (sortedFields.map fun (l, T, _) => (l, T)),
    body := .record (sortedFields.map fun (l, _, t) => (l, t)),
    methods := (Row.sort (methods.map (·, ()))).map (·.1), laws := [], rels }
  return pkg

def activity (S : Ty) (cursor log : Label) (cursorLimit logLimit : Nat)
    (resumer : Term) (plans : List ActivityPlan) : Except ActivityRefusal Package := do
  if plans.isEmpty then throw .noPlans
  if 2 * plans.length + 1 > methodsMax then throw .tooManyPlans
  if !(plans.map (·.name)).Nodup then throw .duplicatePlan
  if cursor = log then throw .sameRelation
  match checkE [] resumer (.fn S (.fn reqTy .bool)) (Ω := []) with
  | .error why => throw (.package (.illTyped why))
  | .ok () => pure ()
  for p in plans do
    for (t, T) in [
      (p.precondition, Ty.fn S (.fn p.captured (.fn reqTy .bool))),
      (p.start, Ty.fn S (.fn p.captured (.fn reqTy S))),
      (p.resume, Ty.fn S (.fn p.captured (.fn p.response (.fn reqTy S))))] do
      match checkE [] t T (Ω := []) with
      | .error why => throw (.package (.illTyped why))
      | .ok () => pure ()
  let pkg := activityPackage S cursor log cursorLimit logLimit resumer plans
  match pkg.checkWith [] with
  | .error why => throw (.package why)
  | .ok () => pure pkg

end Nanodregg.Lang.Std
