/-
# Lang.Surface — the authoring surface (LANG-50): a second reader that lowers to the core

Never in admission. A surface text is read by `Read.parse` (the one s-expression parser); each
declaration's terms are LOWERED to core s-expressions, every core node carrying the offset of the
surface node that made it, and read by `Read.term` (the one core reader); the package is then
assembled, PRINTED (`Print.package`) and READ AGAIN (`Read.readPackage`). So what this module
returns is always a package the core reader read from its own text: a bug here makes a wrong
program, which the checker and the laws judge like any other, never an unread one. A core package
text (`(package (imports …) …)`) is read by `Read.package` unchanged (`read_print_surface`).

    (the grammar is `grammar`, below: one text, which this comment and the testground both read)

An activity precondition/start binds state, arg, req; resume binds state, captured, response,
req. Its cursor and continuation are rows under self. The generated start_name/resume_name
methods and retire method use the same row guards and install checker as handwritten methods.
`(patience n)` (LANG-76, n > 0 heights) adds a `timeout` method: an unanswered row may be retracted
by anyone at or past its key's `notBefore` + n; without it an unanswered row waits for its resumer.

Every annotation the lowering writes comes from a declaration; nothing is inferred, so the
surface never decides a type (the checker does). A method binds `rows state arg req`, a law
`old new req`, a guard `state req edit old` (LANG-59: `old` is the row the edit replaces, as the
caller pinned it). A bounded argument field is checked before the body and refused by name: `refused "text 1..200"` (law 7). `layer` is LANG-18's old-self `extend` over the
imported super package: same state and relations, its laws kept and never overridden
(`Lang.Proofs.Surface.layer_keeps_laws`).
-/
import Lang.StdActivity
import Lang.Print

namespace Nanodregg.Lang.Surface

/-- The surface grammar, as a text a tool shows (the testground's grammar window). -/
def grammar : String :=
  "package ::= (package decl…)\n" ++
  "decl    ::= (type N T) | (state T) | (import N \"hex\") | (layer N) | (doc \"text\")\n" ++
  "          | (rel ℓ (key (f T)…) (val T) (limit n) [(sum f) (cap n)] [(retract)] [(guard g)])\n" ++
  "          | (method ℓ [(reads (rel (points n) | (range m k))…)] [(arg A)] [(calls (kind…)…)] [(edits n)] [(effect (moves n))] body)\n" ++
  "          kind    ::= account | credit | grant | transfer | (invoke T)   — T the argument the invoke sends (LANG-77)\n" ++
  "          | (law ℓ (on occ|(occ…) [x] body)… [(else body)]) | (law ℓ (bounded f max))\n" ++
  "          | (law ℓ (allowlist #hex…)) | (law ℓ (quorum f k #hex…)) | (law ℓ (windowed f W limit))\n" ++
  "          | (activity cursor log [(limits cursorLimit logLimit)] [(patience n)] [(expose m…)]\n" ++
  "              [(guards q w)] [(refusals \"r\" \"u\" \"c\")] (resumer e) plan…)\n" ++
  "          | (machine f initial (methods m…) (from m to)…) | (guard g body)\n" ++
  "plan    ::= (plan name (arg T) (resp U) [(pre e)] (start e) (resume e))\n" ++
  "type    ::= the core's types | N | Req | Verdict | Occasion | AcctRef | Right\n" ++
  "          | (enum ℓ…) | (option T) | (row rel)\n" ++
  "arg A   ::= a type, where a record field may be bounded: (nat lo hi) | (bytes lo hi) | N naming one\n" ++
  "term    ::= the core's terms | x.f.g | ok | (refuse e) | (done state item…) | (with e (f x)…)\n" ++
  "          | (some T e) | (none T) | (N ℓ [e]) | (is N e ℓ) | (all (c \"why\")…)\n" ++
  "          | (check (c \"why\")… body) | (any e…) | (and a b) | (not a) | (index m)\n" ++
  "          | (fold (acc T init) (x rel) step body) | (super m)\n" ++
  "item    ::= (insert rel key val) | (upsert rel key val) | (retract rel key) | (KIND (f e)…)\n"

open Read (SExp ReadRefusal)

/-- Why the surface refuses a text, by name, at a character offset (law 7). -/
inductive Refusal
  | read (e : ReadRefusal)
  | notSurface (pos : Nat)
  | badDecl (pos : Nat)
  | duplicate (pos : Nat) (name : String)
  | unknownType (pos : Nat) (name : String)
  | noState (pos : Nat)
  | boundOutsideArg (pos : Nat)
  | badBound (pos : Nat)
  | missingElse (pos : Nat) (law : String)
  | badClause (pos : Nat)
  | notEnum (pos : Nat) (name : String)
  | noRel (pos : Nat) (name : String)
  | noRange (pos : Nat) (rel : String)
  | tooManyItems (pos : Nat)
  | callKind (pos : Nat) (kind : String)
  | refuseNotLiteral (pos : Nat)
  | outOfPlace (pos : Nat) (word : String)
  | noMethod (pos : Nat) (name : String)
  | std (pos : Nat) (why : String)
  | noSuper (pos : Nat) (name : String)
  | retypedOverride (pos : Nat) (name : String)
  | overridesLaw (pos : Nat) (name : String)
  | layerShape (pos : Nat)
  | unprintable (pos : Nat)
  | reservedBinder (pos : Nat) (name : String)
  /-- `with` naming a field the state does not have, or naming one twice -/
  | noField (pos : Nat) (name : String)
  /-- a layer naming one of its super's relation guards -/
  | overridesGuard (pos : Nat) (name : String)
  /-- a method that did not lower to its four binders -/
  | badShape (pos : Nat)
  deriving Repr

def Refusal.name : Refusal → String
  | .read e => e.name | .notSurface _ => "notSurface" | .badDecl _ => "badDecl"
  | .duplicate _ _ => "duplicate" | .unknownType _ _ => "unknownType" | .noState _ => "noState"
  | .boundOutsideArg _ => "boundOutsideArg" | .badBound _ => "badBound" | .missingElse _ _ => "missingElse"
  | .badClause _ => "badClause" | .notEnum _ _ => "notEnum" | .noRel _ _ => "noRel" | .noRange _ _ => "noRange"
  | .tooManyItems _ => "tooManyItems" | .callKind _ _ => "callKind" | .refuseNotLiteral _ => "refuseNotLiteral"
  | .outOfPlace _ _ => "outOfPlace" | .noMethod _ _ => "noMethod" | .std _ _ => "std" | .noSuper _ _ => "noSuper"
  | .retypedOverride _ _ => "retypedOverride" | .overridesLaw _ _ => "overridesLaw" | .layerShape _ => "layerShape"
  | .unprintable _ => "unprintable" | .reservedBinder _ _ => "reservedBinder"
  | .noField _ _ => "noField" | .overridesGuard _ _ => "overridesGuard" | .badShape _ => "badShape"

def Refusal.pos : Refusal → Nat
  | .read e => e.pos
  | .notSurface p | .badDecl p | .duplicate p _ | .unknownType p _ | .noState p | .boundOutsideArg p
  | .badBound p | .missingElse p _ | .badClause p | .notEnum p _ | .noRel p _ | .noRange p _
  | .tooManyItems p | .callKind p _ | .refuseNotLiteral p | .outOfPlace p _ | .noMethod p _ | .std p _
  | .noSuper p _ | .retypedOverride p _ | .overridesLaw p _ | .layerShape p | .unprintable p
  | .reservedBinder p _ | .noField p _ | .overridesGuard p _ | .badShape p => p

/-- The name, what it is about, and the 1-based line of `text` the offset falls on. -/
def lineOf (text : String) (pos : Nat) : Nat := ((text.toList.take pos).filter (· = '\n')).length + 1

def Refusal.text (src : String) (e : Refusal) : String :=
  let what := match e with
    | .read (.unbound _ x) | .read (.reservedBinder _ x) | .duplicate _ x | .unknownType _ x | .missingElse _ x
    | .notEnum _ x | .noRel _ x | .noRange _ x | .callKind _ x | .outOfPlace _ x | .noMethod _ x | .std _ x
    | .noSuper _ x | .retypedOverride _ x | .overridesLaw _ x | .reservedBinder _ x | .noField _ x
    | .overridesGuard _ x => s!" {x}"
    | _ => ""
  s!"{e.name}{what} line {lineOf src e.pos}"

abbrev P (α : Type) := Except Refusal α

def liftR {α : Type} : Read.P α → P α
  | .ok a => .ok a
  | .error e => .error (.read e)

/-! ## Building core s-expressions at a surface offset -/

def A (p : Nat) (s : String) : SExp := .atom p s
def L (p : Nat) (xs : List SExp) : SExp := .list p xs

mutual
/-- Every offset of a printed form (offsets 0) set to `p`: the surface node that made it. -/
def stamp (p : Nat) : SExp → SExp
  | .atom _ s => .atom p s
  | .str _ s => .str p s
  | .list _ xs => .list p (stampAll p xs)

def stampAll (p : Nat) : List SExp → List SExp
  | [] => []
  | x :: xs => stamp p x :: stampAll p xs
end

def tyAt (p : Nat) (T : Ty) : P SExp :=
  match Print.tySx T with
  | some x => .ok (stamp p x)
  | none => .error (.unprintable p)

def termAt (p : Nat) (t : Term) : P SExp :=
  match Print.termSx 0 t with
  | some x => .ok (stamp p x)
  | none => .error (.unprintable p)

/-! ## Context: what the declarations fix -/

/-- Where a term is: a law or a guard returns a verdict; a method returns its result. -/
inductive Place
  | law
  | guard
  | method (res : Ty) (calls : List Ty) (edits : Nat) (reads : List (Label × RelRead))
  | top

structure Ctx where
  /-- type names, latest first -/
  names : List (String × Ty) := []
  /-- type names of a bounded argument form, as written -/
  boundNames : List (String × SExp) := []
  state : Ty := .record []
  rels : List (Label × RelDecl) := []
  /-- every method label of the package, sorted (`index`) -/
  methods : List Label := []
  activityCode : List (Label × Term) := []
  layered : Bool := false
  place : Place := .top

def builtins : List (String × Ty) :=
  [("Req", reqTy), ("Verdict", verdictTy), ("Occasion", occasionTy), ("AcctRef", acctRefTy), ("Right", rightTy)]

def Ctx.lookupTy (c : Ctx) (n : String) : Option Ty :=
  match c.names.find? (·.1 = n) with
  | some (_, T) => some T
  | none => (builtins.find? (·.1 = n)).map (·.2)

/-- The words the lowering reads as forms; none may be a binder or a type name. -/
def surfaceWords : List String :=
  ["ok", "done", "with", "some", "none", "is", "all", "check", "any", "and", "not", "index", "fold",
   "super", "insert", "upsert", "retract", "refuse", "activity-code"]

/-- A binder name the surface would read as something else. -/
def reservedName (c : Ctx) (x : String) : Bool :=
  Read.isReserved x || surfaceWords.contains x || (c.lookupTy x).isSome || x.contains '.'

def binder (c : Ctx) (p : Nat) (x : String) : P Unit :=
  if reservedName c x then .error (.reservedBinder p x) else .ok ()

/-! ## Types -/

def labelsOf : List SExp → P (List Label)
  | [] => .ok []
  | .atom _ ℓ :: rest => do pure (ℓ :: (← labelsOf rest))
  | x :: _ => .error (.read (.badLabel x.pos))

def entriesWith {α : Type} (f : SExp → P α) : List SExp → P (List (Label × α))
  | [] => .ok []
  | .list _ [.atom _ ℓ, e] :: rest => do pure ((ℓ, ← f e) :: (← entriesWith f rest))
  | x :: _ => .error (.read (.badEntry x.pos))

def relOf (c : Ctx) (p : Nat) (r : String) : P RelDecl :=
  match Row.find? r c.rels with
  | some d => .ok d
  | none => .error (.noRel p r)

def ty (c : Ctx) : Nat → SExp → P Ty
  | 0, x => .error (.read (.tooDeep x.pos))
  | _ + 1, .atom _ "nat" => .ok .nat
  | _ + 1, .atom _ "bool" => .ok .bool
  | _ + 1, .atom _ "bytes" => .ok .bytes
  | _ + 1, .atom _ "digest" => .ok .digest
  | _ + 1, .atom p n =>
    match c.lookupTy n with
    | some T => .ok T
    | none => if (c.boundNames.find? (·.1 = n)).isSome then .error (.boundOutsideArg p) else .error (.unknownType p n)
  | d + 1, .list _ [.atom _ "->", a, b] => do pure (.fn (← ty c d a) (← ty c d b))
  | d + 1, .list _ (.atom _ "rec" :: fs) => do pure (.record (Row.sort (← entriesWith (ty c d) fs)))
  | d + 1, .list _ (.atom _ "sum" :: fs) => do pure (.sum (Row.sort (← entriesWith (ty c d) fs)))
  | _ + 1, .list _ (.atom _ "enum" :: ls) => do pure (Std.stateTy (← labelsOf ls))
  | d + 1, .list _ [.atom _ "option", t] => do pure (optTy (← ty c d t))
  | _ + 1, .list p [.atom _ "row", .atom _ r] => do pure (rowTy (← relOf c p r))
  | _ + 1, .list p [.atom _ "nat", _, _] | _ + 1, .list p [.atom _ "bytes", _, _] => .error (.boundOutsideArg p)
  | _ + 1, x => .error (.read (.notAType x.pos))

/-- A bounded argument field: its path from the argument, which form, and the bound. -/
structure Bound where
  path : List Label
  isBytes : Bool
  lo : Nat
  hi : Nat

def boundOf (p : Nat) (isBytes : Bool) (path : List Label) (lo hi : String) : P (Ty × List Bound) :=
  if path.isEmpty then .error (.boundOutsideArg p) else
  match lo.toNat?, hi.toNat? with
  | some l, some h => if l ≤ h then .ok (if isBytes then .bytes else .nat, [⟨path, isBytes, l, h⟩]) else .error (.badBound p)
  | _, _ => .error (.badBound p)

/-- An argument type, its bounded fields collected in label order. -/
def argTy (c : Ctx) : Nat → List Label → SExp → P (Ty × List Bound)
  | 0, _, x => .error (.read (.tooDeep x.pos))
  | _ + 1, path, .list p [.atom _ "nat", .atom _ lo, .atom _ hi] => boundOf p false path lo hi
  | _ + 1, path, .list p [.atom _ "bytes", .atom _ lo, .atom _ hi] => boundOf p true path lo hi
  | d + 1, path, .list _ (.atom _ "rec" :: fs) => do
    let es ← entriesWith (fun t => pure t) fs
    let rs ← (Row.sort es).mapM fun (ℓ, t) => do
      let (T, bs) ← argTy c d (path ++ [ℓ]) t
      pure ((ℓ, T), bs)
    pure (.record (rs.map (·.1)), (rs.map (·.2)).flatten)
  | d + 1, path, x@(.atom _ n) =>
    match c.boundNames.find? (·.1 = n) with
    | some (_, t) => argTy c d path t
    | none => do pure (← ty c (d + 1) x, [])
  | d + 1, _, x => do pure (← ty c (d + 1) x, [])

/-! ## Terms -/

def okAt (c : Ctx) (p : Nat) : P SExp :=
  match c.place with
  | .law | .guard => do pure (L p [A p "inj", ← tyAt p verdictTy, A p "ok", L p [A p "record"]])
  | _ => .error (.outOfPlace p "ok")

/-- The refusal of the place: a `refused` verdict in a law or guard (any bytes term), the core
`refuse` in a method (a literal reason only: a refusal's name is fixed in the text). -/
def refuseAt (c : Ctx) (p : Nat) (e : SExp) : P SExp :=
  match c.place with
  | .law | .guard => do pure (L p [A p "inj", ← tyAt p verdictTy, A p "refused", e])
  | .method res _ _ _ =>
    match e with
    | .str q w => do pure (L p [A p "refuse", ← tyAt p res, .str q w])
    | _ => .error (.refuseNotLiteral e.pos)
  | .top => .error (.outOfPlace p "refuse")

/-- `x.f.g` for a bound `x`: `(. (. x f) g)`. -/
def dotted (p : Nat) (sc : List String) (a : String) : Option SExp :=
  match a.splitOn "." with
  | x :: f :: fs =>
    if sc.contains x && !(f :: fs).any (·.isEmpty) then
      some ((f :: fs).foldl (fun e g => L p [A p ".", e, A p g]) (A p x))
    else none
  | _ => none

/-- `c1` else refuse `w1`, then `c2` …, then `rest`. -/
def guardsSx (refuse : Nat → String → P SExp) (p : Nat) : List (SExp × Nat × String) → SExp → P SExp
  | [], rest => .ok rest
  | (cnd, q, w) :: more, rest => do
    pure (L p [A p "if", cnd, ← guardsSx refuse p more rest, ← refuse q w])

def anySx (p : Nat) : List SExp → SExp
  | [] => A p "false"
  | e :: es => L p [A p "if", e, A p "true", anySx p es]

/-- A condition with its reason: `(c "why")`. -/
def condOf : SExp → P (SExp × Nat × String)
  | .list _ [c, .str q w] => .ok (c, q, w)
  | x => .error (.badClause x.pos)

/-- One edit or call of `done`. -/
inductive Item
  | edit (e : SExp)
  | call (kind : Label) (payload : SExp)

def sumRow : Ty → List (Label × Ty)
  | .sum r => r
  | _ => []

def recRow : Ty → List (Label × Ty)
  | .record r => r
  | _ => []

/-- The binders of `(fn (x T)… body)`, and its body. -/
def fnParts : List SExp → P (List (Nat × String × SExp) × SExp)
  | [b] => .ok ([], b)
  | .list _ [.atom q x, t] :: rest => do
    let (bs, b) ← fnParts rest
    pure ((q, x, t) :: bs, b)
  | x :: _ => .error (.read (.badBinder x.pos))
  | [] => .error (.read (.badBinder 0))

/-- The arms `(ℓ x body)…` of a case, unread. -/
def armParts : List SExp → P (List (Nat × Label × Nat × String × SExp))
  | [] => .ok []
  | .list p [.atom _ ℓ, .atom q x, b] :: rest => do pure ((p, ℓ, q, x, b) :: (← armParts rest))
  | x :: _ => .error (.read (.badEntry x.pos))

/-- The field entries `(ℓ e)…`, unread. -/
def fieldParts : List SExp → P (List (Nat × Label × SExp))
  | [] => .ok []
  | .list p [.atom _ ℓ, e] :: rest => do pure ((p, ℓ, e) :: (← fieldParts rest))
  | x :: _ => .error (.read (.badEntry x.pos))

def termTy (c : Ctx) (t : SExp) : P SExp := do tyAt t.pos (← ty c Read.depthMax t)

/-- The edit or call slots of `done`, filled in order, the rest `none`. -/
def doneSx (c : Ctx) (p : Nat) (st : SExp) (items : List Item) : P SExp := do
  match c.place with
  | .method _ ks es _ =>
    let edits := items.filterMap fun | .edit e => some e | _ => none
    let calls := items.filterMap fun | .call k e => some (k, e) | _ => none
    if edits.length > es || calls.length > ks.length then throw (.tooManyItems p)
    let E := editTy c.rels
    let eSlots ← (List.range es).mapM fun i => do
      match edits[i]? with
      | some e => pure (L p [A p s!"e{i}", L p [A p "inj", ← tyAt p (optTy E), A p "some", e]])
      | none => pure (L p [A p s!"e{i}", L p [A p "inj", ← tyAt p (optTy E), A p "none", L p [A p "record"]]])
    let cSlots ← (ks.zipIdx).mapM fun (K, i) => do
      match calls[i]? with
      | some (k, e) =>
        if (Row.find? k (sumRow K)).isNone then throw (.callKind p k)
        pure (L p [A p s!"c{i}", L p [A p "inj", ← tyAt p (optTy K), A p "some", L p [A p "inj", ← tyAt p K, A p k, e]]])
      | none => pure (L p [A p s!"c{i}", L p [A p "inj", ← tyAt p (optTy K), A p "none", L p [A p "record"]]])
    pure (L p [A p "record", L p [A p "calls", L p (A p "record" :: cSlots)],
      L p [A p "edits", L p (A p "record" :: eSlots)], L p [A p "state", st]])
  | _ => throw (.outOfPlace p "done")

def callKinds : List Label := (callArms (some (.record []))).map (·.1)

/-- `(with e (f x)…)`: the full state record, each field given or `(. e f)`. -/
def withSx (c : Ctx) (p : Nat) (e : SExp) (given : List (Label × SExp)) : SExp :=
  L p (A p "record" :: (recRow c.state).map fun (f, _) =>
    L p [A p f, (Row.find? f given).getD (L p [A p ".", e, A p f])])

def term (c : Ctx) : Nat → List String → SExp → P SExp
  | 0, _, x => .error (.read (.tooDeep x.pos))
  | _ + 1, _, .list p [.atom _ "activity-code", .atom _ n] =>
    match Row.find? n c.activityCode with
    | some t => termAt p t
    | none => .error (.noMethod p n)
  | _ + 1, sc, x@(.atom p a) =>
    if sc.contains a then .ok x
    else if a = "ok" then okAt c p
    else match dotted p sc a with
      | some e => .ok e
      | none => .ok x
  | _ + 1, _, x@(.str _ _) => .ok x
  | _ + 1, _, x@(.list _ []) => .ok x
  | d + 1, sc, .list p (f@(.atom q h) :: args) =>
    let sub := fun e => term c d sc e
    if sc.contains h then do pure (L p (f :: (← args.mapM sub)))
    else
    match h, args with
    | "lam", [.atom r x, t, b] => do
      binder c r x
      pure (L p [A q "lam", A r x, ← termTy c t, ← term c d (x :: sc) b])
    | "fn", rest => do
      let (bs, b) ← fnParts rest
      for (r, x, _) in bs do binder c r x
      let ts ← bs.mapM fun (r, x, t) => do pure (L r [A r x, ← termTy c t])
      let sc' := bs.foldl (fun s (_, x, _) => x :: s) sc
      pure (L p (A q "fn" :: ts ++ [← term c d sc' b]))
    | "let", [.atom r x, t, e, b] => do
      binder c r x
      pure (L p [A q "let", A r x, ← termTy c t, ← sub e, ← term c d (x :: sc) b])
    | "fix", [e] => do pure (L p [A q "fix", ← sub e])
    | ".", [e, l] => do pure (L p [A q ".", ← sub e, l])
    | "record", fs => do
      let fs ← fieldParts fs
      pure (L p (A q "record" :: (← fs.mapM fun (r, ℓ, e) => do pure (L r [A r ℓ, ← sub e]))))
    | "extend", e :: fs => do
      let fs ← fieldParts fs
      pure (L p (A q "extend" :: (← sub e) :: (← fs.mapM fun (r, ℓ, e) => do pure (L r [A r ℓ, ← sub e]))))
    | "inj", [t, l, e] => do pure (L p [A q "inj", ← termTy c t, l, ← sub e])
    | "case", e :: arms => do
      let as ← armParts arms
      for (_, _, r, x, _) in as do binder c r x
      pure (L p (A q "case" :: (← sub e) ::
        (← as.mapM fun (r, ℓ, s, x, b) => do pure (L r [A r ℓ, A s x, ← term c d (x :: sc) b]))))
    | "if", [a, b, e] => do pure (L p [A q "if", ← sub a, ← sub b, ← sub e])
    | "ref", _ | "digest", _ => .ok (L p (f :: args))
    | "refuse", [t, w] => do pure (L p [A q "refuse", ← termTy c t, w])
    | "refuse", [e] => do refuseAt c p (← sub e)
    | "done", st :: items => do
      let its ← items.mapM fun it =>
        match it with
        | .list r [.atom _ "insert", .atom _ rel, k, v] => do
          let dd ← relOf c r rel
          pure (Item.edit (L r [A r "inj", ← tyAt r (editTy c.rels), A r rel,
            L r [A r "inj", ← tyAt r (relEditTy dd), A r "insert", L r [A r "record", L r [A r "key", ← sub k], L r [A r "val", ← sub v]]]]))
        | .list r [.atom _ "upsert", .atom _ rel, k, v] => do
          let dd ← relOf c r rel
          pure (Item.edit (L r [A r "inj", ← tyAt r (editTy c.rels), A r rel,
            L r [A r "inj", ← tyAt r (relEditTy dd), A r "upsert", L r [A r "record", L r [A r "key", ← sub k], L r [A r "val", ← sub v]]]]))
        | .list r [.atom _ "retract", .atom _ rel, k] => do
          let dd ← relOf c r rel
          pure (Item.edit (L r [A r "inj", ← tyAt r (editTy c.rels), A r rel,
            L r [A r "inj", ← tyAt r (relEditTy dd), A r "retract", L r [A r "record", L r [A r "key", ← sub k]]]]))
        | .list r (.atom _ k :: fs) =>
          if callKinds.contains k then do
            let fs ← fieldParts fs
            pure (Item.call k (L r (A r "record" :: (← fs.mapM fun (s, ℓ, e) => do pure (L s [A s ℓ, ← sub e])))))
          else .error (.badClause r)
        | x => .error (.badClause x.pos)
      doneSx c p (← sub st) its
    | "with", e :: fs => do
      let e' ← sub e
      let fs ← fieldParts fs
      let row := recRow c.state
      let mut seen : List Label := []
      for (r, ℓ, _) in fs do
        if (Row.find? ℓ row).isNone || seen.contains ℓ then throw (.noField r ℓ)
        seen := ℓ :: seen
      let given ← fs.mapM fun (_, ℓ, x) => do pure (ℓ, ← sub x)
      pure (withSx c p e' given)
    | "some", [t, e] => do pure (L p [A q "inj", ← tyAt p (optTy (← ty c Read.depthMax t)), A q "some", ← sub e])
    | "none", [t] => do pure (L p [A q "inj", ← tyAt p (optTy (← ty c Read.depthMax t)), A q "none", L p [A q "record"]])
    | "is", [.atom r n, e, .atom s ℓ] => do
      let row := match c.lookupTy n with | some (.sum row) => row | _ => []
      unless !row.isEmpty && row.all (·.2 = .record []) do throw (.notEnum r n)
      unless (Row.find? ℓ row).isSome do throw (.read (.notOfType s))
      pure (L p (A q "case" :: (← sub e) ::
        row.map fun (x, _) => L p [A p x, A p "_", A p (if x = ℓ then "true" else "false")]))
    | "all", cs => do
      let cs ← cs.mapM condOf
      let cs ← cs.mapM fun (cnd, r, w) => do pure (← sub cnd, r, w)
      guardsSx (fun r w => refuseAt c r (.str r w)) p cs (← okAt c p)
    | "check", parts@(_ :: _) => do
      let cs ← (parts.take (parts.length - 1)).mapM condOf
      let cs ← cs.mapM fun (cnd, r, w) => do pure (← sub cnd, r, w)
      let body := (parts.getLast?).getD (L p [])
      guardsSx (fun r w => refuseAt c r (.str r w)) p cs (← sub body)
    | "any", es => do pure (anySx p (← es.mapM sub))
    | "and", [a, b] => do pure (L p [A q "if", ← sub a, ← sub b, A p "false"])
    | "not", [a] => do pure (L p [A q "if", ← sub a, A p "false", A p "true"])
    | "index", [.atom r m] =>
      match c.methods.findIdx? (· = m) with
      | some i => .ok (A r (toString i))
      | none => .error (.noMethod r m)
    | "fold", [.list _ [.atom r acc, t, init], .list s [.atom _ x, .atom _ rel], step, body] => do
      binder c r acc
      binder c s x
      let k ← match c.place with
        | .method _ _ _ reads =>
          match Row.find? rel reads with
          | some ⟨_, some (_, k), _, _⟩ => pure k
          | _ => throw (.noRange s rel)
        | _ => throw (.noRange s rel)
      let T ← termTy c t
      let step' ← term c d (x :: acc :: sc) step
      let body' ← term c d (acc :: sc) body
      let rowsOf := L s [A s ".", L s [A s ".", L s [A s ".", A s "rows", A s rel], A s "range"], A s "rows"]
      let one (i : Nat) (rest : SExp) : SExp :=
        L s [A s "let", A r acc, T,
          L s [A s "case", L s [A s ".", rowsOf, A s s!"r{i}"], L s [A s "none", A s "_", A r acc], L s [A s "some", A s x, step']],
          rest]
      pure (L p [A q "let", A r acc, T, ← sub init, (List.range k).foldr one body'])
    | "super", [.atom r m] =>
      if c.layered then .ok (L p [A q ".", L p [A q "ref", A q "0"], A r m]) else .error (.outOfPlace p "super")
    | _, _ =>
      match c.lookupTy h, args with
      | some T@(.sum row), [.atom r ℓ] =>
        if (Row.find? ℓ row).isSome then do pure (L p [A q "inj", ← tyAt q T, A r ℓ, L p [A p "record"]])
        else .error (.read (.notOfType r))
      | some T@(.sum _), [.atom r ℓ, e] => do pure (L p [A q "inj", ← tyAt q T, A r ℓ, ← sub e])
      | _, _ => do pure (L p (f :: (← args.mapM sub)))
  | d + 1, sc, .list p xs => do pure (L p (← xs.mapM (term c d sc)))

/-! ## Declarations -/

structure Decls where
  types : List (Nat × String × SExp) := []
  state : Option (Nat × SExp) := none
  rels : List (Nat × String × List SExp) := []
  methods : List (Nat × String × List SExp) := []
  laws : List (Nat × String × List SExp) := []
  guards : List (Nat × String × SExp) := []
  activities : List (Nat × String × String × List SExp) := []
  machines : List (Nat × String × String × List SExp × List SExp) := []
  imports : List (Nat × String × String) := []
  layer : Option (Nat × String) := none
  doc : Option (Nat × String) := none

def declsOf (d : Decls) : List SExp → P Decls
  | [] => .ok { d with types := d.types.reverse, rels := d.rels.reverse, methods := d.methods.reverse,
                       laws := d.laws.reverse, guards := d.guards.reverse, machines := d.machines.reverse,
                       imports := d.imports.reverse, activities := d.activities.reverse }
  | .list p [.atom _ "type", .atom _ n, t] :: rest => declsOf { d with types := (p, n, t) :: d.types } rest
  | .list p [.atom _ "state", t] :: rest =>
    if d.state.isSome then .error (.duplicate p "state") else declsOf { d with state := some (p, t) } rest
  | .list p (.atom _ "rel" :: .atom _ ℓ :: xs) :: rest => declsOf { d with rels := (p, ℓ, xs) :: d.rels } rest
  | .list p (.atom _ "method" :: .atom _ ℓ :: xs) :: rest => declsOf { d with methods := (p, ℓ, xs) :: d.methods } rest
  | .list p (.atom _ "law" :: .atom _ ℓ :: xs) :: rest => declsOf { d with laws := (p, ℓ, xs) :: d.laws } rest
  | .list p [.atom _ "guard", .atom _ g, b] :: rest => declsOf { d with guards := (p, g, b) :: d.guards } rest
  | .list p (.atom _ "activity" :: .atom _ cursor :: .atom _ log :: xs) :: rest =>
    declsOf { d with activities := (p, cursor, log, xs) :: d.activities } rest
  | .list p (.atom _ "machine" :: .atom _ f :: .atom _ i :: .list _ (.atom _ "methods" :: ms) :: es) :: rest =>
    declsOf { d with machines := (p, f, i, ms, es) :: d.machines } rest
  | .list p [.atom _ "import", .atom _ n, .str _ h] :: rest => declsOf { d with imports := (p, n, h) :: d.imports } rest
  | .list p [.atom _ "doc", .str q t] :: rest =>
    if d.doc.isSome then .error (.duplicate p "doc") else declsOf { d with doc := some (q, t) } rest
  | .list p [.atom _ "layer", .atom _ n] :: rest =>
    if d.layer.isSome then .error (.duplicate p "layer") else declsOf { d with layer := some (p, n) } rest
  | x :: _ => .error (.badDecl x.pos)

/-- Each label once among methods, laws, guards and machines. -/
def unique (p : Nat) : List String → List String → P Unit
  | _, [] => .ok ()
  | seen, x :: xs => if seen.contains x then .error (.duplicate p x) else unique p (x :: seen) xs

def relDecl (c : Ctx) (p : Nat) (xs : List SExp) : P RelDecl := do
  let (key, rest) ← match xs with
    | .list _ (.atom _ "key" :: ks) :: rest => do
      let ks ← entriesWith (ty c Read.depthMax) ks
      pure (ks, rest)
    | _ => throw (.badClause p)
  let (val, rest) ← match rest with
    | .list _ [.atom _ "val", v] :: rest => do pure (← ty c Read.depthMax v, rest)
    | _ => throw (.badClause p)
  let (limit, rest) ← match rest with
    | .list q [.atom _ "limit", .atom _ n] :: rest =>
      match n.toNat? with | some n => pure (n, rest) | none => throw (.badClause q)
    | _ => throw (.badClause p)
  let (sum, cap, rest) ← match rest with
    | .list _ [.atom _ "sum", .atom _ f] :: .list q [.atom _ "cap", .atom _ n] :: rest =>
      match n.toNat? with | some n => pure (some f, n, rest) | none => throw (.badClause q)
    | rest => pure (none, 0, rest)
  let (retract, rest) := match rest with
    | .list _ [.atom _ "retract"] :: rest => (true, rest)
    | rest => (false, rest)
  let guard ← match rest with
    | [.list _ [.atom _ "guard", .atom _ g]] => pure (some g)
    | [] => pure none
    | x :: _ => throw (.badClause x.pos)
  pure { key, val, limit, sum, cap, retract, guard }

/-- A method's clauses before its body. -/
structure MethodHead where
  reads : List (Label × RelRead) := []
  arg : SExp := .list 0 [.atom 0 "rec"]
  /-- each slot: its kinds, and the argument type of its `(invoke T)` kind if it has one (LANG-77) -/
  calls : List (List Label × Option SExp) := []
  edits : Nat := 0
  /-- `(effect (moves N))`: the method's grades (LANG-89) -/
  effect : Option Effect := none

def methodHead (h : MethodHead) : List SExp → P (MethodHead × SExp)
  | [b] => .ok (h, b)
  | .list _ (.atom _ "reads" :: rs) :: rest => do
    -- `(live)` last: the points carry their key's cell liveness (E1; a cell-keyed relation only)
    let liveOf : List SExp → List SExp × Bool := fun xs =>
      match xs.getLast? with
      | some (.list _ [.atom _ "live"]) => (xs.dropLast, true)
      | _ => (xs, false)
    -- `(receipt)` after it: the points carry the `receipt` argument checked against the head
    -- object each key names (E5; a cell-keyed relation, an argument with `receipt : bytes`)
    let receiptOf : List SExp → List SExp × Bool := fun xs =>
      match xs.getLast? with
      | some (.list _ [.atom _ "receipt"]) => (xs.dropLast, true)
      | _ => (xs, false)
    let reads ← rs.mapM fun
      | .list p xs =>
        let (xs, receipt) := receiptOf xs
        let (xs, live) := liveOf xs
        match xs with
        | [.atom _ rel, .list _ [.atom _ "points", .atom q n]] =>
          match n.toNat? with | some n => .ok (rel, ⟨n, none, live, receipt⟩) | none => .error (.badClause q)
        | [.atom _ rel, .list _ [.atom _ "range", .atom q m, .atom _ k]] =>
          match m.toNat?, k.toNat? with | some m, some k => .ok (rel, ⟨0, some (m, k), live, receipt⟩) | _, _ => .error (.badClause q)
        | [.atom _ rel, .list _ [.atom _ "points", .atom q n], .list _ [.atom _ "range", .atom _ m, .atom _ k]] =>
          match n.toNat?, m.toNat?, k.toNat? with
          | some n, some m, some k => .ok (rel, ⟨n, some (m, k), live, receipt⟩)
          | _, _, _ => .error (.badClause q)
        | _ => .error (.badClause p)
      | x => .error (.badClause x.pos)
    methodHead { h with reads := Row.sort reads } rest
  | .list _ [.atom _ "arg", a] :: rest => methodHead { h with arg := a } rest
  | .list _ (.atom _ "calls" :: ks) :: rest => do
    -- a slot `(kind…)`: atoms name kinds; `(invoke T)` is the invoke kind with its argument type
    -- (LANG-77). A bare `invoke` atom names no arm: the slot is then empty and install refuses it.
    let calls ← ks.mapM fun
      | .list p kinds => do
        let mut labels : List Label := []
        let mut inv : Option SExp := none
        for k in kinds do
          match k with
          | .atom _ ℓ => labels := labels ++ [ℓ]
          | .list q [.atom _ "invoke", t] =>
            if inv.isSome then throw (.duplicate q "invoke")
            inv := some t
          | x => throw (.read (.badLabel x.pos))
        if labels.isEmpty && inv.isNone then throw (.badClause p)
        pure (labels, inv)
      | x => .error (.badClause x.pos)
    methodHead { h with calls } rest
  | .list _ [.atom _ "edits", .atom q n] :: rest =>
    match n.toNat? with
    | some n => methodHead { h with edits := n } rest
    | none => .error (.badClause q)
  | .list q [.atom _ "effect", .list _ [.atom _ "moves", .atom r n]] :: rest =>
    if h.effect.isSome then .error (.duplicate q "effect") else
    match n.toNat? with
    | some n => methodHead { h with effect := some { moves := n } } rest
    | none => .error (.badClause r)
  | x :: _ => .error (.badClause x.pos)
  | [] => .error (.badClause 0)

/-! ## Bounded argument forms: the check before a method's body (§4.5, LANG-50)

Built on terms, after the one reader read the method: inside a method's four binders the
argument is `var 1`. Each bounded field, in label order, is checked; the first out of its bound
refuses the run by its NAME, `"text 1..200"` (`Lang.Proofs.Surface.boundCheck_meaning`). -/

/-- The argument's field at `path` (the argument is `var 1` under a method's binders). -/
def pathT (path : List Label) : Term := path.foldl (fun e g => .get e g) (.var 1)

/-- The refusal's name: the field's path and its bound. -/
def Bound.name (b : Bound) : String := s!"{".".intercalate b.path} {b.lo}..{b.hi}"

/-- The field is within its bound. -/
def Bound.cond (b : Bound) : Term :=
  let x := pathT b.path
  if b.isBytes then
    if b.lo = 0 then .prim .lenLe x (.nat b.hi)
    else .ite (.prim .lenLe x (.nat (b.lo - 1))) (.bool false) (.prim .lenLe x (.nat b.hi))
  else .ite (.prim .le (.nat b.lo) x) (.prim .le x (.nat b.hi)) (.bool false)

/-- Each bound in order, the first one out refusing by its name; then the body. -/
def boundCheck (res : Ty) : List Bound → Term → Term
  | [], body => body
  | b :: bs, body => .ite b.cond (boundCheck res bs body) (.refuse res b.name.toUTF8)

/-- A method's body under its four binders, checked first. -/
def wrapMethod (p : Nat) (res : Ty) (bs : List Bound) : Term → P Term
  | .lam R (.lam S (.lam A (.lam Q b))) => .ok (.lam R (.lam S (.lam A (.lam Q (boundCheck res bs b)))))
  | _ => .error (.badShape p)

/-- One method, lowered: its type, its core s-expression (the body unchecked), its result type
and its bounds. -/
def methodSx (c : Ctx) (p : Nat) (xs : List SExp) : P (Ty × SExp × Ty × List Bound × Option Effect) := do
  let (h, body) ← methodHead {} xs
  for (rel, _) in h.reads do
    unless (Row.find? rel c.rels).isSome do throw (.noRel p rel)
  let (A', bounds) ← argTy c Read.depthMax [] h.arg
  let R := readsTy c.rels h.reads
  let ks ← h.calls.mapM fun (kinds, inv) => do
    match inv with
    | some t => pure (invokeOf (← ty c Read.depthMax t) kinds)
    | none => pure (callOf kinds)
  let E := editTy c.rels
  let res := resultTy c.state ks E h.edits
  let cm := { c with place := .method res ks h.edits h.reads }
  let b ← term cm Read.depthMax ["req", "arg", "state", "rows"] body
  let sx := L p [A p "lam", A p "rows", ← tyAt p R, L p [A p "lam", A p "state", ← tyAt p c.state,
    L p [A p "lam", A p "arg", ← tyAt p A', L p [A p "lam", A p "req", ← tyAt p reqTy, b]]]]
  pure (methodTy c.state A' ks R E h.edits, sx, res, bounds, h.effect)

def occasions : List Label := ["adopt", "birth", "invoke", "relaw", "retire", "write"]

/-- A law from its `(on …)` clauses and its `else`, which is required unless all six acts are written. -/
def lawSx (c : Ctx) (p : Nat) (ℓ : String) (xs : List SExp) : P SExp := do
  let cl := { c with place := .law }
  let sc := ["req", "new", "old"]
  let mut arms : List (Label × SExp) := []
  let mut dflt : Option SExp := none
  for x in xs do
    match x with
    | .list q [.atom _ "else", b] =>
      if dflt.isSome then throw (.duplicate q "else")
      dflt := some b
    | .list q (.atom _ "on" :: occ :: rest) =>
      let occs ← match occ with
        | .atom _ o => pure [o]
        | .list _ os => labelsOf os
        | y => throw (.badClause y.pos)
      let (nm, b) ← match rest with
        | [b] => pure ("_", b)
        | [.atom r n, b] => do binder c r n; pure (n, b)
        | _ => throw (.badClause q)
      for o in occs do
        unless occasions.contains o do throw (.badClause q)
        if (Row.find? o arms).isSome then throw (.duplicate q o)
        arms := arms ++ [(o, L q [A q o, A q nm, ← term cl Read.depthMax (nm :: sc) b])]
    | y => throw (.badClause y.pos)
  let mut armSx : List SExp := []
  for o in occasions do
    match Row.find? o arms, dflt with
    | some a, _ => armSx := armSx ++ [a]
    | none, some b => armSx := armSx ++ [L p [A p o, A p "_", ← term cl Read.depthMax ("_" :: sc) b]]
    | none, none => throw (.missingElse p ℓ)
  let S ← tyAt p c.state
  pure (L p [A p "lam", A p "old", S, L p [A p "lam", A p "new", S, L p [A p "lam", A p "req", ← tyAt p reqTy,
    L p (A p "case" :: L p [A p ".", A p "req", A p "occasion"] :: armSx)]]])

def stdErr {α : Type} (p : Nat) : Except Std.StdRefusal α → P α
  | .ok a => .ok a
  | .error e => .error (.std p e.name)

def digestOfAtom (p : Nat) : SExp → P ByteArray
  | .atom _ a => match Read.hexBytes? a with | some b => .ok b | none => .error (.badClause p)
  | x => .error (.badClause x.pos)

/-- A law: its `(on …)` clauses, or one Std clause called by name. -/
def lawTerm (c : Ctx) (p : Nat) (ℓ : String) (xs : List SExp) : P SExp :=
  match xs with
  | [.list q [.atom _ "bounded", .atom _ f, .atom _ m]] =>
    match m.toNat? with
    | some m => termAt q (Std.bounded c.state f m)
    | none => .error (.badClause q)
  | [.list q (.atom _ "allowlist" :: ids)] => do
    termAt q (← stdErr q (Std.allowlist c.state (← ids.mapM (digestOfAtom q))))
  | [.list q (.atom _ "quorum" :: .atom _ f :: .atom _ k :: ids)] =>
    match k.toNat?, Row.find? f (recRow c.state) with
    | some k, some T => do
      let T := match T with | .sum r => (Row.find? "set" r).getD T | _ => T
      termAt q (← stdErr q (Std.quorum c.state T (← ids.mapM (digestOfAtom q)) k f))
    | _, _ => .error (.badClause q)
  | [.list q [.atom _ "windowed", .atom _ f, .atom _ w, .atom _ lim]] =>
    match w.toNat?, lim.toNat?, Row.find? f (recRow c.state) with
    | some w, some lim, some T => do
      let T := match T with | .sum r => (Row.find? "set" r).getD T | _ => T
      termAt q (← stdErr q (Std.windowed c.state T w lim f))
    | _, _, _ => .error (.badClause q)
  | _ => lawSx c p ℓ xs

/-- What lowering a package produces: the package as assembled, and each body field's core
s-expression (for locating a checker's path in the surface text). -/
structure Lowered where
  pkg : Package
  /-- each field's core s-expression, and how many bound checks precede its body -/
  fields : List (Label × SExp × Nat)

def readTermAt (sx : SExp) : P Term := liftR (Read.term Read.depthMax [] sx)


/-- Close an activity expression over its documented arguments, then pass it
through the ordinary surface term lowering and core reader. -/
def activityFunction (c : Ctx) (p : Nat) (args : List (String × Ty)) (body : SExp) : P Term := do
  let b ← term c Read.depthMax (args.reverse.map (·.1)) body
  let sx ← args.foldrM (fun (name, T) rest => do
    pure (L p [A p "lam", A p name, ← tyAt p T, rest])) b
  readTermAt sx

/-- Activity surface: plan callbacks return state; resume binds state, captured,
response, req. Each plan may supply a precondition (default true). -/
def activityDecl (c : Ctx) (p : Nat) (cursor log : Label) (xs : List SExp)
    (extraRels : List (Label × RelDecl) := []) (allCode : Bool := false) : P Package := do
  let (cursorLimit, logLimit, rest) ← match xs with
    | .list q [.atom _ "limits", .atom _ a, .atom _ b] :: rest =>
      match a.toNat?, b.toNat? with
      | some a, some b => pure (a, b, rest)
      | _, _ => throw (.badClause q)
    | _ => pure (64, 1024, xs)
  let (patience, rest) ← match rest with
    | .list q [.atom _ "patience", .atom _ n] :: rest =>
      match n.toNat? with
      | some n => pure (some n, rest)
      | none => throw (.badClause q)
    | _ => pure (none, rest)
  let (expose, rest) ← match rest with
    | .list _ (.atom _ "expose" :: names) :: rest =>
      pure (some (← labelsOf names), rest)
    | _ => pure (none, rest)
  let (guardNames, rest) ← match rest with
    | .list _ [.atom _ "guards", .atom _ queued, .atom _ waiting] :: rest =>
      pure (some (queued, waiting), rest)
    | _ => pure (none, rest)
  let (vocabulary, rest) ← match rest with
    | .list _ [.atom _ "refusals", .str _ resumer, .str _ missing, .str _ captured] :: rest =>
      pure (({ notResumer := resumer, unstarted := missing, captured } : Std.ActivityVocabulary), rest)
    | _ => pure ({}, rest)
  let (resumer, rest) ← match rest with
    | .list q [.atom _ "resumer", body] :: rest =>
      pure (← activityFunction c q [("state", c.state), ("req", reqTy)] body, rest)
    | _ => throw (.badClause p)
  let plans ← rest.mapM fun x => do
    match x with
    | .list q (.atom _ "plan" :: .atom _ name ::
        .list _ [.atom _ "arg", K] :: .list _ [.atom _ "resp", R] :: bodies) =>
      let K ← ty c Read.depthMax K
      let R ← ty c Read.depthMax R
      let (pre, bodies) := match bodies with
        | .list _ [.atom _ "pre", pre] :: bs => (pre, bs)
        | bs => (A q "true", bs)
      match bodies with
      | [.list _ [.atom _ "start", start], .list _ [.atom _ "resume", resume]] =>
        pure ({
          name, captured := K, response := R,
          precondition := ← activityFunction c q [("state", c.state), ("arg", K), ("req", reqTy)] pre,
          start := ← activityFunction c q [("state", c.state), ("arg", K), ("req", reqTy)] start,
          resume := ← activityFunction c q
            [("state", c.state), ("captured", K), ("response", R), ("req", reqTy)] resume } : Std.ActivityPlan)
      | _ => throw (.badClause q)
    | _ => throw (.badClause x.pos)
  match Std.activity c.state cursor log cursorLimit logLimit resumer plans patience with
  | .ok _ =>
    let pkg := Std.activityPackage c.state cursor log cursorLimit logLimit resumer plans
      extraRels guardNames vocabulary patience
    match expose with
    | none => pure pkg
    | some ns =>
      for n in ns do
        unless pkg.methods.contains n do throw (.noMethod p n)
      if allCode then pure pkg else
        let keep (n : Label) := !pkg.methods.contains n || ns.contains n
        let .record ts := pkg.iface | throw (.badShape p)
        let .record bs := pkg.body | throw (.badShape p)
        pure { pkg with
          methods := pkg.methods.filter (ns.contains ·),
          iface := .record (ts.filter (keep ∘ Prod.fst)),
          body := .record (bs.filter (keep ∘ Prod.fst)) }
  | .error why => throw (.std p why.name)

/-- Each field the layer adds: never a law of the super (`overridesLaw`), and a field the super
has only at the super's own type (`retypedOverride`). -/
def checkAdds (posOf : Label → Nat) (sup : Package) : List (Label × Ty × Term) → P Unit
  | [] => .ok ()
  | (ℓ, T, _) :: rest =>
    if sup.laws.contains ℓ then .error (.overridesLaw (posOf ℓ) ℓ)
    else if sup.rels.any (·.2.guard = some ℓ) then .error (.overridesGuard (posOf ℓ) ℓ)
    else match Row.find? ℓ (recRow sup.iface) with
      | some T' => if T' = T then checkAdds posOf sup rest else .error (.retypedOverride (posOf ℓ) ℓ)
      | none => checkAdds posOf sup rest

/-- The layer over `sup` (id `sid`): its own fields added to the super's by `extend (ref 0)`;
a law of the super is never overridden and is kept (`Lang.Proofs.Surface.layer_keeps_laws`). -/
def layerOf (posOf : Label → Nat) (sid : ByteArray) (sup : Package) (adds : List (Label × Ty × Term))
    (addLaws addMethods : List Label) : P Package := do
  checkAdds posOf sup adds
  pure { imports := [sid], state := sup.state, rels := sup.rels,
         iface := .record (Row.merge (recRow sup.iface) (Row.sort (adds.map fun (ℓ, T, _) => (ℓ, T)))),
         body := .extend (.ref 0) (Row.sort (adds.map fun (ℓ, _, t) => (ℓ, t))),
         methods := sup.methods ++ addMethods.filter (!sup.methods.contains ·),
         laws := (Row.sort ((sup.laws ++ addLaws).map (·, ()))).map (·.1) }

/-- Lower a surface package's declarations (`supers`: the packages a layer may name, by id). -/
def lower (supers : List (ByteArray × Package)) (p : Nat) (ds : List SExp) : P Lowered := do
  let d ← declsOf {} ds
  -- the doc, as `Read.doc` reads one (LANG-60): never empty when written, `Bounds.docOk`
  let doc ← match d.doc with
    | none => pure ByteArray.empty
    | some (q, t) => liftR (Read.doc q [.str q t])
  -- type names, in order; a bounded form is kept as written (argument types only)
  let mut c : Ctx := {}
  for (q, n, t) in d.types do
    if reservedName c n || (c.boundNames.find? (·.1 = n)).isSome then throw (.duplicate q n)
    match t with
    | .list _ [.atom _ "nat", _, _] | .list _ [.atom _ "bytes", _, _] => c := { c with boundNames := (n, t) :: c.boundNames }
    | _ => c := { c with names := (n, ← ty c Read.depthMax t) :: c.names }
  -- the layer's super, if any
  let sup ← match d.layer with
    | none => pure none
    | some (q, n) =>
      match d.imports.find? (·.2.1 = n) with
      | none => throw (.noSuper q n)
      | some (_, _, h) =>
        match Read.unhex .empty h.toList with
        | none => throw (.read (.badImport q))
        | some b =>
          match supers.find? (·.1 = b) with
          | some (_, P) => pure (some (b, P))
          | none => throw (.noSuper q n)
  if sup.isSome && (d.state.isSome || !d.rels.isEmpty || !d.machines.isEmpty || !d.activities.isEmpty || d.imports.length != 1) then
    throw (.layerShape p)
  let S ← match d.state, sup with
    | some (_, t), _ => ty c Read.depthMax t
    | none, some (_, P) => pure P.state
    | none, none => throw (.noState p)
  let activities ← d.activities.mapM fun (q, cursor, log, xs) => do
    pure (q, ← activityDecl { c with state := S } q cursor log xs)
  let activityMethods := activities.flatMap (·.2.methods)
  let rels ← match sup with
    | some (_, P) => pure P.rels
    | none => do
      let rs ← d.rels.mapM fun (q, ℓ, xs) => do pure (ℓ, ← relDecl { c with state := S } q xs)
      let rs := rs ++ activities.flatMap (·.2.rels)
      unique p [] (rs.map (·.1))
      pure (Row.sort rs)
  let activityParts ← d.activities.mapM fun (q, cursor, log, xs) => do
    let extra := rels.filter fun r => r.1 != cursor && r.1 != log
    pure (q, ← activityDecl { c with state := S } q cursor log xs extra)
  let activityCode ← d.activities.flatMapM fun (q, cursor, log, xs) => do
    let extra := rels.filter fun r => r.1 != cursor && r.1 != log
    let full ← activityDecl { c with state := S } q cursor log xs extra true
    let .record fs := full.body | throw (.badShape q)
    pure (fs.filter (fun f => full.methods.contains f.1))
  unique p [] (activityCode.map (·.1))
  -- a machine names the methods it steps; its edges may name only those (`unknownMethod`)
  let machineMethods ← d.machines.flatMapM fun (_, _, _, ms, _) => labelsOf ms
  let declared := d.methods.map (·.2.1)
  let sorted (ls : List Label) : List Label := ((Row.sort (ls.map (·, ()))).map (·.1)).eraseDups
  -- a layer keeps its super's method indices: the super's methods first, in its order, then the new
  let allMethods := match sup with
    | some (_, P) => P.methods ++ sorted (declared.filter (!P.methods.contains ·))
    | none => sorted (declared ++ machineMethods ++ activityMethods)
  unique p [] (declared ++ machineMethods ++ d.laws.map (·.2.1) ++ d.guards.map (·.2.1) ++ d.machines.map (·.2.1) ++
    activities.flatMap (fun (_, P) => (recRow P.iface).map (·.1)))
  c := { c with state := S, rels, methods := allMethods, activityCode, layered := sup.isSome }
  -- methods
  let ms ← d.methods.mapM fun (q, ℓ, xs) => do
    let (T, sx, res, bs, ef) ← methodSx c q xs
    pure (ℓ, T, sx, res, bs, ef)
  -- machines: the law, and a step method for each method label it names that is not declared
  let mut mlaws : List (Label × SExp × Term) := []
  let mut mmethods : List (Label × Ty × SExp × Term) := []
  for (q, f, init, ms, es) in d.machines do
    let states := match Row.find? f (recRow S) with | some (.sum r) => r.map (·.1) | _ => []
    let edges ← es.mapM fun
      | .list _ [.atom _ x, .atom _ m, .atom _ y] => pure (x, m, y)
      | e => throw (.badClause e.pos)
    let law ← stdErr q (Std.machine S f states init allMethods edges)
    mlaws := mlaws ++ [(f, ← termAt q law, law)]
    for m in ← labelsOf ms do
      unless declared.contains m do
        let t ← stdErr q (Std.stepTo S f states allMethods m edges)
        mmethods := mmethods ++ [(m, methodTy S (.record []), ← termAt q t, t)]
  -- laws and guards
  let ls ← d.laws.mapM fun (q, ℓ, xs) => do pure (ℓ, ← lawTerm c q ℓ xs)
  let gs ← d.guards.mapM fun (q, g, b) => do
    match rels.find? (·.2.guard = some g) with
    | none => throw (.noRel q g)
    | some (_, rd) =>
      let cg := { c with place := .guard }
      -- a guard binds `state req edit old` (LANG-59): its third argument is the guard input
      -- record, bound as `edit` long enough to name its two fields
      let b' ← term cg Read.depthMax ["edit", "old", "req", "state"] b
      pure (g, guardTy S rd, L q [A q "lam", A q "state", ← tyAt q S, L q [A q "lam", A q "req", ← tyAt q reqTy,
        L q [A q "lam", A q "edit", ← tyAt q (guardInTy rd),
          L q [A q "let", A q "old", ← tyAt q (optTy rd.val), L q [A q ".", A q "edit", A q "old"],
            L q [A q "let", A q "edit", ← tyAt q (relEditTy rd), L q [A q ".", A q "edit", A q "edit"], b']]]]])
  -- read every field's core text with the one reader
  let mut fields : List (Label × Ty × Term) := []
  let mut sxs : List (Label × SExp × Nat) := []
  for (ℓ, T, sx, res, bs, _) in ms do
    fields := fields ++ [(ℓ, T, ← wrapMethod sx.pos res bs (← readTermAt sx))]; sxs := sxs ++ [(ℓ, sx, bs.length)]
  -- the grades (LANG-89), by method label ascending; a layer may not re-grade an inherited method
  let effects := Row.sort (ms.filterMap fun (ℓ, _, _, _, _, ef) => ef.map (ℓ, ·))
  if let some (_, P) := sup then
    for (ℓ, _) in effects do
      if P.methods.contains ℓ then throw (.retypedOverride p ℓ)
  for (ℓ, T, sx, t) in mmethods do
    fields := fields ++ [(ℓ, T, t)]; sxs := sxs ++ [(ℓ, sx, 0)]
  for (ℓ, sx, t) in mlaws do
    fields := fields ++ [(ℓ, lawTy S, t)]; sxs := sxs ++ [(ℓ, sx, 0)]
  for (ℓ, sx) in ls do
    fields := fields ++ [(ℓ, lawTy S, ← readTermAt sx)]; sxs := sxs ++ [(ℓ, sx, 0)]
  for (g, T, sx) in gs do
    fields := fields ++ [(g, T, ← readTermAt sx)]; sxs := sxs ++ [(g, sx, 0)]
  for (q, P) in activityParts do
    match P.iface, P.body with
    | .record ts, .record bs =>
      for (l, T) in ts do
        match Row.find? l bs with
        | some t =>
          fields := fields ++ [(l, T, t)]
          sxs := sxs ++ [(l, ← termAt q t, 0)]
        | none => throw (.badShape q)
    | _, _ => throw (.badShape q)
  let lawLabels := d.laws.map (·.2.1) ++ mlaws.map (·.1)
  match sup with
  | some (sid, P) =>
    -- a layer's doc is its own (the super's is the super's)
    pure ⟨{ ← layerOf (fun ℓ => ((Row.find? ℓ sxs).map (·.1.pos)).getD p) sid P fields lawLabels
      (allMethods.drop P.methods.length) with doc, effects := Row.sort (P.effects ++ effects) }, sxs⟩
  | none =>
    let imports ← d.imports.mapM fun (q, _, h) =>
      match Read.unhex .empty h.toList with
      | some b => pure b
      | none => throw (.read (.badImport q))
    pure ⟨{ imports, state := S, rels,
            iface := .record (Row.sort (fields.map fun (ℓ, T, _) => (ℓ, T))),
            body := .record (Row.sort (fields.map fun (ℓ, _, t) => (ℓ, t))),
            methods := allMethods,
            laws := (Row.sort (lawLabels.map (·, ()))).map (·.1), doc, effects }, sxs⟩

/-- A core package text: `(package (imports …) …)`. -/
def isCore : SExp → Bool
  | .list _ (.atom _ "package" :: .list _ (.atom _ "imports" :: _) :: _) => true
  | _ => false

/-- The package a text means, with each field's core s-expression (empty for a core text). The
surface's package is printed and read again by the one reader; a core text is read as it is. -/
def readSExpWith (supers : List (ByteArray × Package)) (x : SExp) : P Lowered :=
  if isCore x then do pure ⟨← liftR (Read.package x), []⟩
  else match x with
    | .list p (.atom _ "package" :: ds) => do
      let l ← lower supers p ds
      match Print.package l.pkg with
      | some t => do pure ⟨← liftR (Read.readPackage t), l.fields⟩
      | none => throw (.unprintable p)
    | y => .error (.notSurface y.pos)

def readWith (supers : List (ByteArray × Package)) (text : String) : P Lowered := do
  readSExpWith supers (← liftR (Read.parse text))

/-- Text (surface or core) to a package: the surface's one entry point. -/
def readPackage (text : String) : P Package := do pure (← readWith [] text).pkg

/-! ## Locating a checker's path in the text -/

/-- The offset of the node a `TypeErr` path (LANG-27) names in a core s-expression, as far as the
path can be followed; the form's own offset where it cannot. -/
def locate : Nat → SExp → List String → Nat
  | 0, x, _ => x.pos
  | _ + 1, x, [] => x.pos
  | n + 1, x@(.list _ (.atom _ h :: args)), seg :: rest =>
    let go (y : SExp) := locate n y rest
    match h, args, seg with
    | "lam", [_, _, b], "body" => go b
    | "let", [_, _, _, b], "fn" => match rest with | "body" :: r => locate n b r | _ => x.pos
    | "let", [_, _, e, _], "arg" => go e
    | "fix", [e], "fix" => go e
    | ".", [e, _], "target" => go e
    | "extend", e :: _, "target" => go e
    | "case", e :: _, "target" => go e
    | "if", [c, _, _], "cond" => go c
    | "if", [_, a, _], "then" => go a
    | "if", [_, _, b], "else" => go b
    | "inj", [_, _, e], _ => go e
    | _, [a, _], "left" => go a
    | _, [_, b], "right" => go b
    | "record", fs, ℓ | "extend", _ :: fs, ℓ =>
      match fs.find? (fun | .list _ (.atom _ k :: _) => k = ℓ | _ => false) with
      | some (.list _ [_, e]) => go e
      | _ => x.pos
    | "case", _ :: arms, ℓ =>
      match arms.find? (fun | .list _ (.atom _ k :: _) => k = ℓ | _ => false) with
      | some (.list _ [_, _, b]) => go b
      | _ => x.pos
    | _, _, _ => x.pos
  | _ + 1, x, _ => x.pos

/-- `k` leading `then` segments dropped (a method's bound checks), if they are there. -/
def dropThen : Nat → List String → Option (List String)
  | 0, r => some r
  | k + 1, "then" :: r => dropThen k r
  | _ + 1, _ => none

/-- The offset a body-check path points to: its first segment is the field; past a method's four
binders, its bound checks are skipped (a path into a check points at the method). -/
def locateField (l : Lowered) : List String → Option Nat
  | ℓ :: rest => (Row.find? ℓ l.fields).map fun (sx, k) =>
    if k = 0 then locate (rest.length + 1) sx rest else
    match rest with
    | "body" :: "body" :: "body" :: "body" :: r =>
      match dropThen k r with
      | some r' => locate (rest.length + 1) sx (["body", "body", "body", "body"] ++ r')
      | none => sx.pos
    | _ => sx.pos
  | [] => none

/-- The core text a surface text lowers to (printed), if it lowers. -/
def coreText (src : String) : Option String := (readPackage src).toOption.bind Print.package

/-- A shipped package's row (LANG-50, ROOT's condition 1): its surface source lowers to EXACTLY the
core text shipped beside it, which is exactly the builder's package printed; and the source with one
token flipped (`flip`) lowers to something else or is refused, so the row can go red. -/
def shippedRow (tag : String) (src core : String) (want : Package) (flip : String × String) : String × Bool :=
  let same := coreText src == some core && Print.package want == some core
  let mutated := src.replace flip.1 flip.2
  -- the planted source must still lower (a refusal would pass for the wrong reason) and differ
  let caught := mutated != src && (coreText mutated).isSome && coreText mutated != some core
  (s!"{tag} the surface source ({src.length} chars) lowers to the shipped core ({core.length} chars) byte for byte: {same}; plant {flip.1} -> {flip.2} caught: {caught}",
    same && caught)

/-- The source's digest under its own domain: what binds a text to the package it lowers to is a
computation (lower, print, encode, compare), so this digest is never stored in the package. -/
def domSource : String := "nanodregg/lang/source/v1"

end Nanodregg.Lang.Surface
