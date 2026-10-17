/-
# Lang.Std — the law library: generators of closed core terms (decisions/lang.md LANG-20)

A stdlib law is a Lean function that EMITS a closed term of type `lawTy S`; a package is composed at
author time (`pkgOf`: one state type, one authority law, any further laws, the methods), and its id
commits to the expanded terms. Nothing here runs at admission: the receiver runs the emitted term
like any other law (`Lang.Law.runLaw`). What each law MEANS is a theorem in `Lang.Proofs.Std`,
proved over the reference semantics (`BigStep`), never by evaluating the term.

Every law is built by `lawOf S birth relaw change`, which cases on `req.occasion` with an arm for
every act (KERNEL's `Occasion`, LANG-19): the birth clause judges the seed, the relaw clause the
replacement of a data object's laws (it sees the new law ids' bytes), the change clause every write
and invoke. There is no default arm: each law states what it does at a birth and at a relaw.

Clauses are written against `At`, which knows how many binders sit between the law's three
arguments and the clause, so a clause may open a `case` of its own (`At.under`) and still name
`old`, `new` and `req` correctly. Labels are the author's: `pkgOf` sorts rows into canonical order;
a law over a field its state type lacks fails the install check (`illTyped`), never at run time.
-/
import Lang.Package
import Lang.Data

namespace Nanodregg.Lang.Std

/-- Where a clause sits: `depth` binders below the law's `old`, `new`, `req`. -/
structure At where
  depth : Nat

namespace At
def old (a : At) : Term := .var (a.depth + 2)
def new (a : At) : Term := .var (a.depth + 1)
def req (a : At) : Term := .var a.depth
/-- One binder further in (inside an arm of a `case` the clause opens itself). -/
def under (a : At) : At := ⟨a.depth + 1⟩
/-- The occasion's payload (`lawOf`'s arm binder, one binder below the law's arguments): in a
relaw clause the incoming laws' bytes, in an invoke clause the method index. -/
def payload (a : At) : Term := .var (a.depth - 1)
def oldF (a : At) (f : Label) : Term := .get a.old f
def newF (a : At) (f : Label) : Term := .get a.new f
def reqF (a : At) (f : Label) : Term := .get a.req f
end At

/-! ## Verdicts and combinators -/

def okT : Term := .inj verdictTy "ok" (.record [])
def refusedT (why : String) : Term := .inj verdictTy "refused" (.bytes why.toUTF8)

/-- `c` must hold, else refuse with `why`; then `rest`. -/
def guard (c : Term) (why : String) (rest : Term) : Term := .ite c rest (refusedT why)

/-- Each condition in order, each with its reason; `rest` if all hold. -/
def guards : List (Term × String) → Term → Term
  | [], t => t
  | (c, w) :: r, t => guard c w (guards r t)

/-- Every condition, then `ok`. -/
def allOf (l : List (Term × String)) : Term := guards l okT

def andT (a b : Term) : Term := .ite a b (.bool false)
def notT (a : Term) : Term := .ite a (.bool false) (.bool true)

/-- Some condition holds (`false` for none). -/
def anyOf : List Term → Term
  | [] => .bool false
  | c :: r => .ite c (.bool true) (anyOf r)

def natT (k : Nat) : Term := .nat k

/-- Rows into canonical order (the order `pkgOf` and `Read` give them). -/
def insertRow {α : Type} (x : Label × α) : List (Label × α) → List (Label × α)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertRow x ys

/-- Stable insertion sort by label, structural so the kernel can evaluate it (`decide +kernel`
over a generated package; `List.mergeSort` is well-founded and does not reduce there). -/
def sortRow {α : Type} (fs : List (Label × α)) : List (Label × α) := fs.foldr insertRow []

/-- Why a generator refuses its parameters (law 7): a law it emitted would mean something other
than its name says, or nothing at all. -/
inductive StdRefusal
  /-- a quorum member listed twice would hold two votes -/
  | duplicateMember
  /-- a quorum threshold outside `1 ≤ k ≤ members` (k = 0 commits unapproved) -/
  | badThreshold
  /-- more members than mask bits below `2^64` -/
  | tooManyMembers
  /-- an epoch of width 0 (every act would fault) -/
  | zeroWidth
  | duplicateState
  | unknownState (state : Label)
  | unknownMethod (method : Label)
  deriving DecidableEq, Repr

def StdRefusal.name : StdRefusal → String
  | .duplicateMember => "duplicateMember" | .badThreshold => "badThreshold"
  | .tooManyMembers => "tooManyMembers" | .zeroWidth => "zeroWidth"
  | .duplicateState => "duplicateState" | .unknownState _ => "unknownState"
  | .unknownMethod _ => "unknownMethod"

def need (c : Bool) (e : StdRefusal) : Except StdRefusal Unit := if c then .ok () else .error e

/-- The law skeleton: `λ old new req. case req.occasion` with one arm per act. In every arm the
payload is `var 0` and the clause sits at depth 1; the `adopt` and `relaw` clauses also receive the
incoming laws' bytes (`At.payload`). `adopt` is this law judging the state it is being ADDED over
(KERNEL-27: after the laws in force admitted `relaw laws'`, each incoming law judges the unchanged
state); `relaw` is this law, in force, judging its replacement. -/
def lawCase5 (birth adopt relaw write invoke : At → Term) : Term :=
  let a : At := ⟨1⟩
  .case (.get (.var 0) "occasion")
    [("adopt", adopt a), ("birth", birth a), ("invoke", invoke a), ("relaw", relaw a), ("write", write a)]

/-- A law with one clause per act. -/
def lawOf5 (S : Ty) (birth adopt relaw write invoke : At → Term) : Term :=
  .lam S (.lam S (.lam reqTy (lawCase5 birth adopt relaw write invoke)))

/-- The common case: writes and invokes judged alike, as a CHANGE. -/
def lawCase (birth adopt relaw change : At → Term) : Term := lawCase5 birth adopt relaw change change

def lawOf (S : Ty) (birth adopt relaw change : At → Term) : Term :=
  .lam S (.lam S (.lam reqTy (lawCase birth adopt relaw change)))

/-! ## Authority narrowing

Authority is the kernel's. Once KERNEL-25 lands (ruled 10-17, NOT YET BUILT: invoke owner-gated
like write; a stranger refused `noGrant` before any law runs), every admitted write, law
replacement and invoke has as its `principal` the object's owner, reached directly or through a
grant chain rooted at the owner; today a write or relaw already does, an invoke does not. A law
only NARROWS that authority. So there is no "owner acts" law (it would re-check the kernel's gate
against a copy of the owner in state, a twin) and no "anyone" law (strangers never reach a law). -/

/-- The signer is the principal, so no delegate acts through a grant. With KERNEL-25 that is
"only the owner's own key"; before it, an invoke without a grant has principal = signer = anyone. -/
def ownerSigns (S : Ty) : Term :=
  let c (a : At) := allOf [(.prim .beq (a.reqF "agent") (a.reqF "principal"), "not signed by the owner")]
  lawOf S c c c c

/-- Only the listed members (`agent`, the signer) may create, change or re-law the object. -/
def allowlist (S : Ty) (ids : List ByteArray) : Term :=
  let listed (a : At) := anyOf (ids.map fun i => .prim .beq (a.reqF "agent") (.bytes i))
  let c (a : At) := allOf [(listed a, "not on the allowlist")]
  lawOf S c c c c

/-! ## Bounds -/

/-- Natural field `f` is at most `max` in every state the object reaches, its seed included. -/
def bounded (S : Ty) (f : Label) (max : Nat) : Term :=
  let c (a : At) := allOf [(.prim .le (a.newF f) (natT max), s!"{f} over {max}")]
  lawOf S c c (fun _ => okT) c

/-! ## Quorum: k of n members approve one proposal, which is then the only change admitted

State fields (besides the author's): `approvals : nat`, a bitmask over `members` (bit i: member i
approved the CURRENT proposal); `proposal : proposalTy T`, either `set v` (field `guarded` becomes
`v`) or `laws L` (a data object's laws are replaced by exactly `L`, the ids' bytes concatenated).
A change is exactly one of:
* commit: `guarded` changes, only to the proposed `v`, with ≥ k approvals, and approvals reset to 0;
* propose: `guarded` unchanged, `proposal` changes, approvals reset to 0;
* approve: only `approvals` changes, by the SIGNER's own bit, which was unset;
* no-op: nothing the law watches changes.
Every change and relaw is by a member (`agent`); a birth (by the creator, who is the owner) has
no approvals. A relaw needs ≥ k approvals of exactly the incoming laws (and consumes none: a relaw
cannot change state, so the same relaw may be replayed, which is idempotent). Any member may
propose, which resets every approval: a member can stall the quorum (liveness, not safety).
`quorum` refuses duplicate members (one member, two votes), `k` outside `1 ≤ k ≤ members`, and
more than 63 members (a mask bit is a natural below `2^64`). `quorumLaw` is the unchecked term,
what the theorems are about. -/

def proposalTy (T : Ty) : Ty := .sum [("laws", .bytes), ("set", T)]

def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

/-- Equality at the guarded field's type (`nat` or `bytes`; any other type is refused by install,
because `eq` is typed at `nat`). -/
def eqAt (T : Ty) (x y : Term) : Term := if T = .bytes then .prim .beq x y else .prim .eq x y

/-- Bit `i` of a mask, as `0` or `1`. -/
def bit (t : Term) (i : Nat) : Term := .prim .mod (.prim .div t (natT (pow2 i))) (natT 2)

/-- The number of set bits among the first `cnt`. -/
def popcount (t : Term) (cnt : Nat) : Term :=
  (List.range cnt).foldl (fun acc i => .prim .add acc (bit t i)) (natT 0)

/-- What `popcount` computes, in Lean: the set bits among the first `cnt` of `a`. -/
def popcountNat (a cnt : Nat) : Nat :=
  (List.range cnt).foldl (fun acc i => acc + a / pow2 i % 2) 0

/-- The signer is a member. -/
def isMember (members : List ByteArray) (a : At) : Term :=
  anyOf (members.map fun m => .prim .beq (a.reqF "agent") (.bytes m))

/-- `p` and `q` (proposals of `proposalTy T`, as clauses) are the same proposal. Inside the inner
arm `var 0` is `q`'s payload and `var 1` is `p`'s. -/
def sameProposal (T : Ty) (a : At) (p q : At → Term) : Term :=
  .case (p a)
    [("laws", .case (q a.under) [("laws", .prim .beq (.var 0) (.var 1)), ("set", .bool false)]),
     ("set", .case (q a.under) [("laws", .bool false), ("set", eqAt T (.var 0) (.var 1))])]

/-- The old proposal is `set v` with `v` the new value of `guarded`. -/
def proposedSet (T : Ty) (guarded : Label) (a : At) : Term :=
  .case (a.oldF "proposal") [("laws", .bool false), ("set", eqAt T (.var 0) (a.under.newF guarded))]

/-- The old proposal is `laws L` with `L` the incoming laws (a relaw clause only). -/
def proposedLaws (a : At) : Term :=
  .case (a.oldF "proposal") [("laws", .prim .beq (.var 0) a.under.payload), ("set", .bool false)]

/-- An approval: member `i` (the signer) sets its own bit, which was unset. -/
def approvalBy (a : At) (m : ByteArray) (i : Nat) : Term :=
  andT (.prim .eq (bit (a.oldF "approvals") i) (natT 0))
    (andT (.prim .eq (a.newF "approvals") (.prim .add (a.oldF "approvals") (natT (pow2 i))))
      (.prim .beq (a.reqF "agent") (.bytes m)))

def quorumLaw (S T : Ty) (members : List ByteArray) (k : Nat) (guarded : Label) : Term :=
  let cnt := members.length
  let quorate (a : At) := Term.prim .le (natT k) (popcount (a.oldF "approvals") cnt)
  let reset (a : At) := Term.prim .eq (a.newF "approvals") (natT 0)
  let change (a : At) : Term :=
    guards [(isMember members a, "not a member"),
            (.prim .lt (a.newF "approvals") (natT (pow2 cnt)), "approvals out of range")]
      (.ite (notT (eqAt T (a.newF guarded) (a.oldF guarded)))
        (allOf [(quorate a, "no quorum"), (proposedSet T guarded a, "not the proposal"),
                (reset a, "approvals not reset")])
        (.ite (notT (sameProposal T a (fun b => b.newF "proposal") (fun b => b.oldF "proposal")))
          (allOf [(reset a, "approvals not reset")])
          (.ite (.prim .eq (a.newF "approvals") (a.oldF "approvals")) okT
            (guard (anyOf (members.zipIdx.map fun (m, i) => approvalBy a m i)) "not an approval" okT))))
  let relawC (a : At) := guards [(isMember members a, "not a member")]
    (allOf [(quorate a, "no quorum"), (proposedLaws a, "not the proposal")])
  lawOf S
    (fun a => allOf [(reset a, "approvals at birth")])
    relawC relawC
    change

def quorum (S T : Ty) (members : List ByteArray) (k : Nat) (guarded : Label) : Except StdRefusal Term := do
  need (members.length ≤ 63) .tooManyMembers
  need (decide members.Nodup) .duplicateMember
  need (1 ≤ k && k ≤ members.length) .badThreshold
  pure (quorumLaw S T members k guarded)

/-! ## Rate: at most `limit` changes of `guarded` per epoch of `W` heights

State fields: `count : nat`, `epoch : nat`. The call's signed window (`notBefore`, `validUntil`,
which `World.admit` enforces) must lie inside one epoch, `notBefore / W`, and the state's epoch is
that one; within it `count` rises by one for each change of `guarded`, up to `limit`; a later epoch
restarts it (at most `limit` there too). No clock holder: the epoch is read from the window the
signer committed to. `windowed` refuses `W = 0`; `windowedLaw` is the unchecked term. -/

def windowedLaw (S T : Ty) (W limit : Nat) (guarded : Label) : Term :=
  let e (a : At) := Term.prim .div (a.reqF "notBefore") (natT W)
  let inOneEpoch (a : At) : List (Term × String) :=
    [(.prim .eq (.prim .div (a.reqF "validUntil") (natT W)) (e a), "window spans epochs"),
     (.prim .eq (a.newF "epoch") (e a), "epoch is not the call's window")]
  let inc (a : At) := Term.ite (eqAt T (a.newF guarded) (a.oldF guarded)) (natT 0) (natT 1)
  let fresh (a : At) := guards (inOneEpoch a) (allOf [(.prim .eq (a.newF "count") (natT 0), "count at birth")])
  lawOf S fresh fresh
    (fun _ => okT)
    (fun a => guards (inOneEpoch a)
      (.ite (.prim .eq (a.newF "epoch") (a.oldF "epoch"))
        (allOf [(.prim .eq (a.newF "count") (.prim .add (a.oldF "count") (inc a)), "count not bumped"),
                (.prim .le (a.newF "count") (natT limit), s!"rate limit {limit}")])
        (allOf [(.prim .lt (a.oldF "epoch") (a.newF "epoch"), "epoch went back"),
                (.prim .eq (a.newF "count") (inc a), "count not reset"),
                (.prim .le (a.newF "count") (natT limit), s!"rate limit {limit}")])))

def windowed (S T : Ty) (W limit : Nat) (guarded : Label) : Except StdRefusal Term := do
  need (0 < W) .zeroWidth
  pure (windowedLaw S T W limit guarded)

/-! ## Machines: a finite-state field moved only by methods along named edges

Field `f` is a sum of empty records over `states`. A birth starts at `initial`; an invoke of method
`m` moves `f` from `a` to `b` only along an edge `(a, m, b)`; a write or a relaw is refused (for a
programmed object the kernel refuses both before any law runs, `hasMethods`: the arm is defence in
depth). `stepTo` is the method that takes the edge. -/

/-- The type of a machine field over `states`. -/
def stateTy (states : List Label) : Ty := .sum (sortRow (states.map fun s => (s, .record [])))

/-- `t` (a term of `stateTy states`) is the state `s`. -/
def isState (states : List Label) (t : Term) (s : Label) : Term :=
  .case t ((sortRow (states.map fun x => (x, ()))).map fun (x, _) => (x, .bool (decide (x = s))))

def machineLaw (S : Ty) (f : Label) (states : List Label) (initial : Label)
    (edges : List (Label × Nat × Label)) : Term :=
  let frozen (_ : At) := refusedT "a machine changes only by its methods"
  let start (a : At) := allOf [(isState states (a.newF f) initial, s!"{f} does not start at {initial}")]
  lawOf5 S start start
    frozen frozen
    (fun a => allOf [(anyOf (edges.map fun (x, m, y) =>
      andT (.prim .eq a.payload (natT m))
        (andT (isState states (a.oldF f) x) (isState states (a.newF f) y))), "no edge")])

/-- The method that takes edge `(old.f, m, _)`: every field of `S` kept, `f` set to the first such
edge's target, or kept (then `machine` refuses). `S` must be a record type. -/
def stepLaw (S : Ty) (f : Label) (states : List Label) (m : Nat) (edges : List (Label × Nat × Label)) : Term :=
  let row := match S with | .record r => r | _ => []
  let target (x : Label) : Label := ((edges.find? fun (a, k, _) => a = x && k = m).map (·.2.2)).getD x
  let next : Term := .case (.get (.var 2) f)
    ((sortRow (states.map fun x => (x, ()))).map fun (x, _) => (x, .inj (stateTy states) (target x) (.record [])))
  .lam S (.lam (.record []) (.lam reqTy
    (.record (row.map fun (ℓ, _) => (ℓ, if ℓ = f then next else .get (.var 2) ℓ)))))

/-- A method's index in a package: its place among the package's method labels in `pkgOf`'s
(sorted) order. -/
def methodIndex (methods : List Label) (m : Label) : Option Nat :=
  go ((sortRow (methods.map fun x => (x, ()))).map (·.1)) 0
where
  go : List Label → Nat → Option Nat
    | [], _ => none
    | x :: xs, i => if x = m then some i else go xs (i + 1)

/-- Edges named by method LABEL, resolved to indices among the package's `methods`, every state
named. -/
def resolveEdges (states methods : List Label) (edges : List (Label × Label × Label)) :
    Except StdRefusal (List (Label × Nat × Label)) :=
  edges.mapM fun (x, m, y) => do
    need (states.contains x) (.unknownState x)
    need (states.contains y) (.unknownState y)
    match methodIndex methods m with
    | some i => pure (x, i, y)
    | none => throw (.unknownMethod m)

/-- The machine law, edges `(from, method label, to)` over the package's `methods` labels. -/
def machine (S : Ty) (f : Label) (states : List Label) (initial : Label) (methods : List Label)
    (edges : List (Label × Label × Label)) : Except StdRefusal Term := do
  need (decide states.Nodup) .duplicateState
  need (states.contains initial) (.unknownState initial)
  pure (machineLaw S f states initial (← resolveEdges states methods edges))

/-- The method `m` (a label among `methods`) of a machine: takes its edge. -/
def stepTo (S : Ty) (f : Label) (states : List Label) (methods : List Label) (m : Label)
    (edges : List (Label × Label × Label)) : Except StdRefusal Term := do
  need (decide states.Nodup) .duplicateState
  match methodIndex methods m with
  | some i => pure (stepLaw S f states i (← resolveEdges states methods edges))
  | none => throw (.unknownMethod m)

/-! ## Packages -/


/-- A package over state `S`: its laws and its methods `(label, argument type, term)`, rows sorted
into canonical order. Authority is the kernel's (KERNEL-25); the laws only narrow it. -/
def pkgOf (S : Ty) (laws : List (Label × Term)) (methods : List (Label × Ty × Term)) : Package :=
  let laws := sortRow laws
  let ms := sortRow methods
  { imports := [], state := S,
    iface := .record (sortRow (laws.map (fun (l, _) => (l, lawTy S)) ++ ms.map (fun (l, A, _) => (l, methodTy S A)))),
    body := .record (sortRow (laws ++ ms.map (fun (l, _, t) => (l, t)))),
    methods := ms.map (·.1), laws := laws.map (·.1) }

/-- A method: `λ state arg req. {fields}` with the state at `var 2`, the argument at `var 1`. -/
def methodOf (S A : Ty) (fields : List (Label × Term)) : Term :=
  .lam S (.lam A (.lam reqTy (.record (sortRow fields))))

/-- The body under a law's three binders (a stdlib law is always `λ old new req. body`). -/
def lawBody : Term → Term
  | .lam _ (.lam _ (.lam _ b)) => b
  | t => t

/-- What every law's statement below assumes of its environment: request, new, old as data. -/
abbrev LawEnv (rq n o : Data) (E : Env) : Env := rq.toVal :: n.toVal :: o.toVal :: E

end Nanodregg.Lang.Std
