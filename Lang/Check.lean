/-
# Lang.Check — the type checker, a total function (DECISIONS LANG-3)

`inferE Δ Γ t` is the type of `t` under the closure's package types `Δ` (indexed by `ref`) and
the local types `Γ` (indexed by `var`), or the rule that failed, by name, with the PATH to the
subterm where it failed (`TypeErr`: outermost segment first; `fn`/`arg`, a field or arm label,
`target`, `cond`/`then`/`else`, …). `infer` is its `toOption`: one checker, and the reason is
never lost on the way to a refusal (law 7). It is syntax-directed and annotation-driven,
O(size of `t` × size of the types it compares). `Lang.Proofs.Check` proves it equal to the typing
relation `HasType` (sound and complete), so a term's type is unique.

Bounds are typing facts: a literal natural must be below `Bounds.natLimit` and a literal byte
string at most `Bounds.bytesMax` and a literal digest at most `Bounds.digestBytesMax`, so every value a checked program starts from is in bounds.
A `case` must have at least one arm (its result type comes from the arms).
-/
import Lang.Bounds
import Lang.Term

namespace Nanodregg.Lang

/-- Which typing rule a term breaks (law 7: each a constructor with a name). -/
inductive TypeError
  /-- `var i` with fewer than `i + 1` binders in scope -/
  | unbound (index : Nat)
  /-- `ref i` past the closure -/
  | noPackage (index : Nat)
  /-- an annotation (a `lam` domain, an `inj` type) whose rows are not canonical -/
  | badType (ty : Ty)
  | notFunction (got : Ty)
  | argument (expected got : Ty)
  /-- `fix t` with `t` not of type `R → R` for a record type `R` -/
  | notSelfMap (got : Ty)
  | natRange (value : Nat)
  | bytesRange (size : Nat)
  /-- an id literal longer than `Bounds.digestBytesMax` -/
  | digestRange (size : Nat)
  | operands (p : Prim) (left right : Ty)
  /-- a record literal's or an extension's labels are not strictly ascending -/
  | notCanonical
  | notRecord (got : Ty)
  | noField (label : Label)
  /-- an `inj` annotation or a `case` scrutinee that is not a sum -/
  | notSum (got : Ty)
  | noArm (label : Label)
  | payload (expected got : Ty)
  /-- a `case`'s arms do not follow the sum's labels one for one, in order -/
  | arms
  | armType (first other : Ty)
  | condition (got : Ty)
  | branches (whenTrue whenFalse : Ty)
  /-- a checked term's type is not the declared one -/
  | declared (expected got : Ty)
  deriving DecidableEq, Repr

def TypeError.name : TypeError → String
  | .unbound _ => "unbound" | .noPackage _ => "noPackage" | .badType _ => "badType"
  | .notFunction _ => "notFunction" | .argument _ _ => "argument" | .notSelfMap _ => "notSelfMap"
  | .natRange _ => "natRange" | .bytesRange _ => "bytesRange" | .digestRange _ => "digestRange" | .operands _ _ _ => "operands"
  | .notCanonical => "notCanonical" | .notRecord _ => "notRecord" | .noField _ => "noField"
  | .notSum _ => "notSum" | .noArm _ => "noArm" | .payload _ _ => "payload" | .arms => "arms"
  | .armType _ _ => "armType" | .condition _ => "condition" | .branches _ _ => "branches"
  | .declared _ _ => "declared"

/-- A failed rule and where: the path from the checked term to the subterm, outermost first. -/
structure TypeErr where
  path : List String
  error : TypeError
  deriving DecidableEq, Repr

/-- One segment further out. -/
def TypeErr.at (seg : String) (e : TypeErr) : TypeErr := { e with path := seg :: e.path }

/-- `name @path` (the convention of a `program` reason: the first token is the name). -/
def TypeErr.text (e : TypeErr) : String :=
  s!"{e.error.name} @{if e.path.isEmpty then "top" else ".".intercalate e.path}"

/-- The rule `e` fails at this node. -/
def typeErr (e : TypeError) : Except TypeErr Ty := .error ⟨[], e⟩

mutual
def inferE (Δ Γ : List Ty) : Term → Except TypeErr Ty
  | .var i =>
      match Γ[i]? with
      | some T => .ok T
      | none => typeErr (.unbound i)
  | .lam A b =>
      if A.wf then
        match inferE Δ (A :: Γ) b with
        | .ok B => .ok (.fn A B)
        | .error e => .error (e.at "body")
      else typeErr (.badType A)
  | .app f a =>
      match inferE Δ Γ f, inferE Δ Γ a with
      | .ok (.fn A B), .ok A' => if A = A' then .ok B else typeErr (.argument A A')
      | .ok F, .ok _ => typeErr (.notFunction F)
      | .error e, _ => .error (e.at "fn")
      | .ok _, .error e => .error (e.at "arg")
  | .fix t =>
      match inferE Δ Γ t with
      | .ok (.fn (.record r) (.record r')) =>
          if r = r' then .ok (.record r) else typeErr (.notSelfMap (.fn (.record r) (.record r')))
      | .ok F => typeErr (.notSelfMap F)
      | .error e => .error (e.at "fix")
  | .nat n => if n < Bounds.natLimit then .ok .nat else typeErr (.natRange n)
  | .bool _ => .ok .bool
  | .bytes s => if s.size ≤ Bounds.bytesMax then .ok .bytes else typeErr (.bytesRange s.size)
  | .digest s => if s.size ≤ Bounds.digestBytesMax then .ok .digest else typeErr (.digestRange s.size)
  | .prim p a b =>
      match inferE Δ Γ a, inferE Δ Γ b with
      | .ok A, .ok B => if A = p.left ∧ B = p.right then .ok p.result else typeErr (.operands p A B)
      | .error e, _ => .error (e.at "left")
      | .ok _, .error e => .error (e.at "right")
  | .record fs =>
      if Row.ascending fs then
        match inferFields Δ Γ fs with
        | .ok r => .ok (.record r)
        | .error e => .error e
      else typeErr .notCanonical
  | .get t ℓ =>
      match inferE Δ Γ t with
      | .ok (.record r) =>
          match Row.find? ℓ r with
          | some T => .ok T
          | none => typeErr (.noField ℓ)
      | .ok T => typeErr (.notRecord T)
      | .error e => .error (e.at "target")
  | .extend t fs =>
      match inferE Δ Γ t with
      | .ok (.record r) =>
          if Row.ascending fs then
            match inferFields Δ Γ fs with
            | .ok r2 => .ok (.record (Row.merge r r2))
            | .error e => .error e
          else typeErr .notCanonical
      | .ok T => typeErr (.notRecord T)
      | .error e => .error (e.at "target")
  | .inj T ℓ t =>
      match T with
      | .sum r =>
          if T.wf then
            match Row.find? ℓ r, inferE Δ Γ t with
            | some A, .ok A' => if A = A' then .ok T else typeErr (.payload A A')
            | none, _ => typeErr (.noArm ℓ)
            | some _, .error e => .error (e.at ℓ)
          else typeErr (.badType T)
      | T => typeErr (.notSum T)
  | .case t arms =>
      match inferE Δ Γ t with
      | .ok (.sum r) => inferArms Δ Γ arms r
      | .ok T => typeErr (.notSum T)
      | .error e => .error (e.at "target")
  | .ite c t e =>
      match inferE Δ Γ c, inferE Δ Γ t, inferE Δ Γ e with
      | .ok .bool, .ok A, .ok B => if A = B then .ok A else typeErr (.branches A B)
      | .ok C, .ok _, .ok _ => typeErr (.condition C)
      | .error x, _, _ => .error (x.at "cond")
      | .ok _, .error x, _ => .error (x.at "then")
      | .ok _, .ok _, .error x => .error (x.at "else")
  | .ref i =>
      match Δ[i]? with
      | some T => .ok T
      | none => typeErr (.noPackage i)

/-- The row of a list of fields, label for label (an error is under its field's label). -/
def inferFields (Δ Γ : List Ty) : List (Label × Term) → Except TypeErr (List (Label × Ty))
  | [] => .ok []
  | (ℓ, t) :: fs =>
      match inferE Δ Γ t, inferFields Δ Γ fs with
      | .ok T, .ok r => .ok ((ℓ, T) :: r)
      | .error e, _ => .error (e.at ℓ)
      | .ok _, .error e => .error e

/-- The common type of the arms of a case over the sum row `r`: one arm per label, in order,
each binding its payload; at least one arm (an error is under its arm's label). -/
def inferArms (Δ Γ : List Ty) : List (Label × Term) → List (Label × Ty) → Except TypeErr Ty
  | [(ℓ, b)], [(ℓ', A)] =>
      if ℓ = ℓ' then
        match inferE Δ (A :: Γ) b with
        | .ok B => .ok B
        | .error e => .error (e.at ℓ)
      else .error ⟨[], .arms⟩
  | (ℓ, b) :: arms@(_ :: _), (ℓ', A) :: r =>
      if ℓ = ℓ' then
        match inferE Δ (A :: Γ) b, inferArms Δ Γ arms r with
        | .ok B, .ok B' => if B = B' then .ok B else .error ⟨[], .armType B B'⟩
        | .error e, _ => .error (e.at ℓ)
        | .ok _, .error e => .error e
      else .error ⟨[], .arms⟩
  | _, _ => .error ⟨[], .arms⟩
end

/-- The type of `t`, if it has one: `inferE` without the reason. -/
def infer (Δ Γ : List Ty) (t : Term) : Option Ty := (inferE Δ Γ t).toOption

/-- A closed term checked against its declared type, or why not. -/
def checkE (Δ : List Ty) (t : Term) (T : Ty) : Except TypeErr Unit :=
  match inferE Δ [] t with
  | .ok T' => if T' = T then .ok () else .error ⟨[], .declared T T'⟩
  | .error e => .error e

/-- A closed term checked against its declared type. -/
def check (Δ : List Ty) (t : Term) (T : Ty) : Bool := (checkE Δ t T).toBool

/-- The closure's bodies are closed and have the types `ref` gives them. -/
def checkLib (Δ : List Ty) (lib : List Term) : Bool :=
  lib.length == Δ.length && (lib.zip Δ).all fun p => check Δ p.1 p.2

end Nanodregg.Lang
