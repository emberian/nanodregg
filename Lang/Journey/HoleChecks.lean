/- Refusal rows for each generated hole method/guard prefix, with typed plants. -/
import Lang.Journey.Hole

namespace Nanodregg.Lang.Std

private def noneD : Data := .inj "none" (.record [])
private def someD (d : Data) : Data := .inj "some" d
private def dg (s : String) : Data := .digest s.toUTF8
private def st (accepted : Bool := false) (selected : Data := someD (dg "c")) : Data :=
  .record [("accepted", .bool accepted), ("acceptor", dg "b"), ("cap", .nat 10),
    ("chooser", dg "a"), ("closes", .nat 10), ("selected", selected)]
private def req (agent : String := "a") (endTime : Nat := 5) : Data :=
  .record [("agent", dg agent), ("notBefore", .nat 1),
    ("occasion", .inj "invoke" (.nat 0)), ("principal", dg agent),
    ("self", dg "self"), ("validUntil", .nat endTime)]
private def cand : Data := .record [("blocker", noneD), ("by", dg "a"),
  ("reason", .bytes .empty), ("s0", noneD), ("s1", noneD),
  ("status", .inj "verified" (.record [])), ("value", .nat 7)]
private def change (d : Data) (field : Label) (v : Data) : Data :=
  match d with
  | .record fs => .record (fs.map fun (n, x) => (n, if n == field then v else x))
  | _ => d
private def point (key : String := "c") (value : Data := someD cand) : Data :=
  someD (.record [("key", .record [("cand", dg key)]), ("val", value)])
private def rows (p : Data := point) : Data :=
  .record [("candidates", .record [("p0", p)]),
    ("facts", .record [("p0", noneD), ("p1", noneD), ("p2", noneD)])]
private def arg : Data := .record [("cand", dg "c")]
private def proposal : Data := .record [("cand", dg "c"), ("s0", noneD), ("s1", noneD), ("value", .nat 7)]

private def quoted : Nat → Ty → Data → Term
  | 0, _, _ => .nat 0
  | _+1, _, .nat n => .nat n
  | _+1, _, .bool b => .bool b
  | _+1, _, .bytes b => .bytes b
  | _+1, _, .digest b => .digest b
  | n+1, .record ts, .record ds =>
    .record (ds.map fun (l,d) => (l, quoted n ((Row.find? l ts).getD .nat) d))
  | n+1, T@(.sum ts), .inj l d => .inj T l (quoted n ((Row.find? l ts).getD .nat) d)
  | _+1, _, _ => .nat 0

/-- A plant removes a named refusal with a value of the SAME type. The package
checker runs over every mutated package before any verdict is accepted. -/
private def plant : Nat → String → Term → Term
  | 0, _, t => t
  | n+1, why, t =>
    let go := plant n why
    match t with
    | .refuse T w =>
      if w = why.toUTF8 then
        if T = .bool then .bool true
        else if T = .digest then quoted 20 T (dg "c")
        else if T = holeCandidate .nat then quoted 20 T cand
        else if T = .record [("key", keyTy (holeCandidates .nat)), ("val", optTy (holeCandidate .nat))]
          then quoted 20 T (.record [("key", .record [("cand", dg "c")]), ("val", someD cand)])
        else t
      else t
    | .inj _ "refused" (.bytes w) => if w = why.toUTF8 then okT else t
    | .lam T b => .lam T (go b)
    | .app f a => .app (go f) (go a)
    | .fix b => .fix (go b)
    | .prim p a b => .prim p (go a) (go b)
    | .record fs => .record (fs.map fun (l,b) => (l,go b))
    | .get a l => .get (go a) l
    | .extend a fs => .extend (go a) (fs.map fun (l,b) => (l,go b))
    | .inj T l a => .inj T l (go a)
    | .case a fs => .case (go a) (fs.map fun (l,b) => (l,go b))
    | .ite a b c => .ite (go a) (go b) (go c)
    | _ => t

private def outcome (body : Term) (name : Label) (xs : List Data) : String :=
  let env := (xs.map Data.toVal).reverse
  let args := ((List.range xs.length).reverse).map Term.var
  match (Machine.mk []).force 10000 (activityApply (.get body name) args) env with
  | .error (.refused why) => String.fromUTF8! why
  | .error _ => "fault"
  | .ok (.inj "refused" (.bytes why), _) => String.fromUTF8! why
  | .ok _ => "ok"

private def edit (op : Label) (key old value : Data) : Data :=
  .record [("edit", .inj op (.record (if op == "retract" then [("key", key)]
    else [("key", key), ("val", value)]))), ("old", old)]

/-- Name, wanted refusal, actual result. A disabled check makes its row RED,
while the mutated package must still typecheck. -/
def holeCheckRows (disabled : Option String := none) : List (String × String × String) := Id.run do
  let pkg := holePackage .nat holeCapClause
  let body := match disabled with | none => pkg.body | some why => plant 400 why pkg.body
  let .ok () := ({ pkg with body }).checkWith [] | return [("plant-type", "ok", "illTyped")]
  let method (label method : String) (state args request view : Data) (want : String) :=
    (label, want, outcome body method [view,state,args,request])
  let guard (label field : String) (input : Data) (want : String) :=
    (label,want,outcome body field [st,req,input])
  let ck := Data.record [("cand",dg "c")]
  let fk := Data.record [("cell",dg "f")]
  let fact := Data.record [("by",dg "a"),("pin",dg "p")]
  let foreign := change fact "by" (dg "b")
  return [
    method "select-chooser" "select" st arg (req "b") rows "notChooser",
    method "select-accepted" "select" (st true) arg req rows "accepted",
    method "select-point" "select" st arg req (rows noneD) "unknown",
    method "select-row" "select" st arg req (rows (point "c" noneD)) "unknown",
    method "select-key" "select" st arg req (rows (point "other")) "unknown",
    method "propose-window" "propose" st proposal (req "a" 11) rows "closed",
    method "fill-window" "fill" st proposal (req "a" 11) rows "closed",
    method "accept-acceptor" "accept" st (.record []) req rows "notAcceptor",
    method "accept-accepted" "accept" (st true) (.record []) (req "b") rows "accepted",
    method "accept-selected" "accept" (st false noneD) (.record []) (req "b") rows "unselected",
    guard "fact-insert-owner" "posted" (edit "insert" fk noneD foreign) "notYours",
    guard "fact-upsert-unknown" "posted" (edit "upsert" fk noneD fact) "unknown",
    guard "fact-upsert-owner" "posted" (edit "upsert" fk (someD foreign) foreign) "notYours",
    guard "fact-upsert-transfer" "posted" (edit "upsert" fk (someD fact) foreign) "notYours",
    guard "fact-retract-owner" "posted" (edit "retract" fk (someD foreign) fact) "notYours",
    guard "fact-retract-unknown" "posted" (edit "retract" fk noneD fact) "unknown",
    guard "candidate-upsert-unknown" "proposed" (edit "upsert" ck noneD cand) "unknown",
    guard "candidate-value" "proposed" (edit "upsert" ck (someD cand) (change cand "value" (.nat 8))) "value",
    guard "candidate-author" "proposed" (edit "upsert" ck (someD cand) (change cand "by" (dg "b"))) "by",
    guard "candidate-support0" "proposed" (edit "upsert" ck (someD cand)
      (change cand "s0" (someD (.record [("cell",dg "f"),("pin",dg "p")])))) "s0",
    guard "candidate-support1" "proposed" (edit "upsert" ck (someD cand)
      (change cand "s1" (someD (.record [("cell",dg "f"),("pin",dg "p")])))) "s1",
    guard "candidate-status" "proposed" (edit "upsert" ck (someD cand)
      (change cand "status" (.inj "conflict" (.bytes "clause".toUTF8)))) "status",
    ("candidate-pruner","notChooser",outcome body "proposed" [st,req "b",
      edit "upsert" ck (someD cand) (change cand "reason" (.bytes "new".toUTF8))]),
    guard "candidate-insert-author" "proposed" (edit "insert" ck noneD (change cand "by" (dg "b"))) "notYours",
    ("shape-acceptor","acceptor",outcome body "shape" [st,change st "acceptor" (dg "a"),req]),
    ("shape-cap","cap",outcome body "shape" [st,change st "cap" (.nat 11),req]),
    ("shape-chooser","chooser",outcome body "shape" [st,change st "chooser" (dg "b"),req]),
    ("shape-closes","closes",outcome body "shape" [st,change st "closes" (.nat 11),req])]

end Nanodregg.Lang.Std
