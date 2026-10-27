/-
# Lang.Quote — a nano term that writes a package's bytes (LANG-87; DESIGN-META §3)

A TEMPLATE is an open `Term`: a free variable (`var i` with `i` at or past the binders above it)
stands for a stage-1 PARAMETER, a value the generator holds when it runs (`Param.fetch`: the term that
fetches it, e.g. `get (var 1) "max"`). `quoteTerm ps d buf t` is a nano term that appends to the
byte string `buf` the package-wire bytes of `t` with each free variable replaced by its parameter's
LITERAL — cross-stage persistence, as MetaML lifts a stage-1 value into a bracket — and
`quotePackage ps buf p` the bytes of the package `p` so filled (`Wire.encodePackage`), version byte
and all. The emitted term is built from `cat` over literal fragments (every closed subtree is one
fragment, written by the ordinary encoder at authoring time), the three payload writers of LANG-87
(`u64be` a nat parameter, `sized` a bytes one, `dsized` a digest one) and `ite` for a bool one; a
node's framing is `Tree.putD`'s own prefix (`frame`), not a second spelling of the codec.

What it means is `Lang.Proofs.Quote.quotePackage_sound`: under an environment where each parameter
term evaluates to a scalar of its declared type, the quoted term evaluates to exactly
`encodePackage (fillPackage vals p)`, the bytes the Lean generator would have written at those
values — so a nano generator written with this module IS its Lean specification, byte for byte,
and `checkInstall` at the nested install checks what the specification's theorems are about.

Hygiene is the wire's: a parameter enters the generated code only as a literal node; a `var` of the
template below its binders is a bound variable of the GENERATED program and is written as one.
-/
import Lang.Package
import Lang.Eval

namespace Nanodregg.Lang

open Nanodregg.Codec

/-! ## Closedness and filling: the specification side -/

mutual
/-- No variable at or past `d` is free in `t`. -/
def Term.closedAt (d : Nat) : Term → Bool
  | .var i => decide (i < d)
  | .lam _ b => Term.closedAt (d + 1) b
  | .app f a => Term.closedAt d f && Term.closedAt d a
  | .fix t => Term.closedAt d t
  | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => true
  | .prim _ a b => Term.closedAt d a && Term.closedAt d b
  | .record fs => Term.closedFields d fs
  | .get t _ => Term.closedAt d t
  | .extend t fs => Term.closedAt d t && Term.closedFields d fs
  | .inj _ _ t => Term.closedAt d t
  | .case t arms => Term.closedAt d t && Term.closedFields (d + 1) arms
  | .ite c a b => Term.closedAt d c && Term.closedAt d a && Term.closedAt d b
  | .hole _ σ => Term.closedTerms d σ

def Term.closedFields (d : Nat) : List (Label × Term) → Bool
  | [] => true
  | (_, t) :: fs => Term.closedAt d t && Term.closedFields d fs

def Term.closedTerms (d : Nat) : List Term → Bool
  | [] => true
  | t :: ts => Term.closedAt d t && Term.closedTerms d ts
end

/-- The literal of a scalar value; a non-scalar has none. -/
def Val.lit? : Val → Option Term
  | .nat n => some (.nat n)
  | .bool v => some (.bool v)
  | .bytes s => some (.bytes s)
  | .digest s => some (.digest s)
  | _ => none

mutual
/-- `t` with each free variable `var i` (`i ≥ d`) replaced by the literal of `vals[i - d]`, when that
is a scalar; any other free variable stays. The specification of `quoteTerm`. -/
def Term.fill (vals : List Val) (d : Nat) : Term → Term
  | .var i => if i < d then .var i else
      match vals[i - d]? with
      | some v => (v.lit?).getD (.var i)
      | none => .var i
  | .lam A b => .lam A (Term.fill vals (d + 1) b)
  | .app f a => .app (Term.fill vals d f) (Term.fill vals d a)
  | .fix t => .fix (Term.fill vals d t)
  | .nat n => .nat n
  | .bool v => .bool v
  | .bytes s => .bytes s
  | .digest s => .digest s
  | .ref i => .ref i
  | .refuse T w => .refuse T w
  | .prim p a b => .prim p (Term.fill vals d a) (Term.fill vals d b)
  | .record fs => .record (Term.fillFields vals d fs)
  | .get t ℓ => .get (Term.fill vals d t) ℓ
  | .extend t fs => .extend (Term.fill vals d t) (Term.fillFields vals d fs)
  | .inj A ℓ t => .inj A ℓ (Term.fill vals d t)
  | .case t arms => .case (Term.fill vals d t) (Term.fillFields vals (d + 1) arms)
  | .ite c a b => .ite (Term.fill vals d c) (Term.fill vals d a) (Term.fill vals d b)
  | .hole n σ => .hole n (Term.fillTerms vals d σ)

def Term.fillFields (vals : List Val) (d : Nat) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, Term.fill vals d t) :: Term.fillFields vals d fs

def Term.fillTerms (vals : List Val) (d : Nat) : List Term → List Term
  | [] => []
  | t :: ts => Term.fill vals d t :: Term.fillTerms vals d ts
end

/-- A package whose body is a template, filled. -/
def fillPackage (vals : List Val) (p : Package) : Package := { p with body := p.body.fill vals 0 }

namespace Quote

/-- A stage-1 parameter: the type of the scalar a free variable stands for, and the term that
fetches it where the quoted term runs (`fetch`). -/
structure Param where
  ty : Ty
  fetch : Term

/-! ## The fragments: the codec's own bytes -/

/-- `cat buf (bytes b)`: literal bytes appended. -/
def lit (buf : Term) (b : ByteArray) : Term := .prim .cat buf (.bytes b)

/-- A node's bytes before its payload: `tag ‖ varint len`. -/
def head (tag : UInt8) (len : Nat) : ByteArray := Stream.u8.bytes tag ++ Stream.varint.bytes len

/-- A node's bytes after its payload: its child count. -/
def tail (k : Nat) : ByteArray := Stream.varint.bytes k

/-- A node's bytes before its children: `tag ‖ varint |p| ‖ p ‖ varint k`, the prefix `Tree.putD`
writes (`Lang.Proofs.Quote.putD_frame`). -/
def frame (tag : UInt8) (p : ByteArray) (k : Nat) : ByteArray := head tag p.size ++ p ++ tail k

/-- A closed tree's bytes, as the package codec writes them. -/
def treeBytes (t : Tree) : ByteArray := Tree.putD Wire.depthMax t ByteArray.empty

/-- A parameter's literal node, written at run time from the parameter's value: a `nat` by `u64be`
(tag 4, an eight-byte payload), `bytes` by `sized` (tag 6), a `digest` by `dsized` (tag 16), a
`bool` by `ite` over the two literal nodes (tag 5). Any other declared type is not a scalar: the
variable is written as a bound one, and the specification (`Term.fill`) leaves it too. -/
def param (buf : Term) (i : Nat) : Option Param → Term
  | some ⟨.nat, x⟩ => lit (.prim .u64be (lit buf (head 4 8)) x) (tail 0)
  | some ⟨.bytes, x⟩ => lit (.prim .sized (lit buf (Stream.u8.bytes 6)) x) (tail 0)
  | some ⟨.digest, x⟩ => lit (.prim .dsized (lit buf (Stream.u8.bytes 16)) x) (tail 0)
  | some ⟨.bool, x⟩ =>
      .ite x (lit buf (frame 5 (Stream.bool.bytes true) 0)) (lit buf (frame 5 (Stream.bool.bytes false) 0))
  | _ => lit buf (treeBytes (Wire.termTree (.var i)))

/-! ## The quoter -/

mutual
/-- A nano term appending to `buf` the bytes of the template `t` under `d` binders, its free
variables written from the parameters `ps`. A closed subterm is one literal fragment. -/
def quoteTerm (ps : List Param) (d : Nat) (buf : Term) : Term → Term
  | .var i => if i < d then lit buf (treeBytes (Wire.termTree (.var i))) else param buf i ps[i - d]?
  | .lam A b =>
      if Term.closedAt (d + 1) b then lit buf (treeBytes (Wire.termTree (.lam A b)))
      else quoteTerm ps (d + 1) (lit buf (frame 1 .empty 2 ++ treeBytes (Wire.tyTree A))) b
  | .app f a =>
      if Term.closedAt d (.app f a) then lit buf (treeBytes (Wire.termTree (.app f a)))
      else quoteTerm ps d (quoteTerm ps d (lit buf (frame 2 .empty 2)) f) a
  | .fix t =>
      if Term.closedAt d t then lit buf (treeBytes (Wire.termTree (.fix t)))
      else quoteTerm ps d (lit buf (frame 3 .empty 1)) t
  | .nat n => lit buf (treeBytes (Wire.termTree (.nat n)))
  | .bool v => lit buf (treeBytes (Wire.termTree (.bool v)))
  | .bytes s => lit buf (treeBytes (Wire.termTree (.bytes s)))
  | .digest s => lit buf (treeBytes (Wire.termTree (.digest s)))
  | .ref i => lit buf (treeBytes (Wire.termTree (.ref i)))
  | .refuse T w => lit buf (treeBytes (Wire.termTree (.refuse T w)))
  | .prim p a b =>
      if Term.closedAt d (.prim p a b) then lit buf (treeBytes (Wire.termTree (.prim p a b)))
      else quoteTerm ps d (quoteTerm ps d (lit buf (frame 7 (Stream.u8.bytes (Wire.primCode p)) 2)) a) b
  | .record fs =>
      if Term.closedFields d fs then lit buf (treeBytes (Wire.termTree (.record fs)))
      else quoteFields ps d (lit buf (frame 8 .empty fs.length)) fs
  | .get t ℓ =>
      if Term.closedAt d t then lit buf (treeBytes (Wire.termTree (.get t ℓ)))
      else quoteTerm ps d (lit buf (frame 9 ℓ.toUTF8 1)) t
  | .extend t fs =>
      if Term.closedAt d (.extend t fs) then lit buf (treeBytes (Wire.termTree (.extend t fs)))
      else quoteFields ps d (quoteTerm ps d (lit buf (frame 10 .empty (fs.length + 1))) t) fs
  | .inj A ℓ t =>
      if Term.closedAt d t then lit buf (treeBytes (Wire.termTree (.inj A ℓ t)))
      else quoteTerm ps d (lit buf (frame 11 ℓ.toUTF8 2 ++ treeBytes (Wire.tyTree A))) t
  | .case t arms =>
      if Term.closedAt d (.case t arms) then lit buf (treeBytes (Wire.termTree (.case t arms)))
      else quoteFields ps (d + 1) (quoteTerm ps d (lit buf (frame 12 .empty (arms.length + 1))) t) arms
  | .ite c a b =>
      if Term.closedAt d (.ite c a b) then lit buf (treeBytes (Wire.termTree (.ite c a b)))
      else quoteTerm ps d (quoteTerm ps d (quoteTerm ps d (lit buf (frame 13 .empty 3)) c) a) b
  | .hole n σ =>
      if Term.closedTerms d σ then lit buf (treeBytes (Wire.termTree (.hole n σ)))
      else quoteTerms ps d (lit buf (frame 18 (Wire.u32Bytes n) σ.length)) σ

/-- The fields of a record, each a `node 15 ℓ [t]`. -/
def quoteFields (ps : List Param) (d : Nat) (buf : Term) : List (Label × Term) → Term
  | [] => buf
  | (ℓ, t) :: fs => quoteFields ps d (quoteTerm ps d (lit buf (frame 15 ℓ.toUTF8 1)) t) fs

def quoteTerms (ps : List Param) (d : Nat) (buf : Term) : List Term → Term
  | [] => buf
  | t :: ts => quoteTerms ps d (quoteTerm ps d buf t) ts
end

/-- The package tree's sections after the body (methods, laws, relations, doc, holes, grades, claims), closed. -/
def sectionsAfter (p : Package) : ByteArray :=
  treeBytes (.node 1 .empty (p.methods.map Wire.labelLeaf)) ++
    treeBytes (.node 1 .empty (p.laws.map Wire.labelLeaf)) ++
    treeBytes (.node 2 .empty (p.rels.map Wire.relTree)) ++ treeBytes (.node 0 p.doc []) ++
    treeBytes (.node 3 .empty (p.holes.map Wire.holeROMTree)) ++
    treeBytes (.node 4 .empty (p.effects.map Wire.effectTree)) ++
    treeBytes (.node 5 .empty (p.claims.map Wire.claimTree))

/-- The package's bytes before the body: the version byte, the package node's frame, and the
imports, state and interface sections, closed. -/
def sectionsBefore (p : Package) : ByteArray :=
  ByteArray.mk #[Bounds.packageWireVersion] ++ frame 0 .empty 11 ++
    treeBytes (.node 0 .empty (p.imports.map fun d => .node 0 d [])) ++
    treeBytes (Wire.tyTree p.state) ++ treeBytes (Wire.tyTree p.iface)

/-- A nano term appending to `buf` the bytes `Wire.encodePackage` writes for `p` with its body's
free variables written from `ps`: one literal fragment before the body, the body quoted, one after. -/
def quotePackage (ps : List Param) (buf : Term) (p : Package) : Term :=
  lit (quoteTerm ps 0 (lit buf (sectionsBefore p)) p.body) (sectionsAfter p)

end Quote
end Nanodregg.Lang
