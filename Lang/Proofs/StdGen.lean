/-
# Lang.Proofs.StdGen — what a generator's run returns (LANG-86)

`generate_run_sound`: every admitted run of `generatorOf b doc`'s one method returns exactly the call
`install b` and no row acts, whatever the state, argument, view and budget. With KERNEL-75's
`tree_package_checked` (the kernel checks what an object installs) and `romIdOf` (the cell is the
content digest), that is the receipt of a generation: the Turn that invoked the generator bore the
cell of `b`, checked. That the head generator has bytes a member
can install is GN0's row, not a theorem (no `native_decide` in the census).
-/
import Lang.StdGen
import Lang.Proofs.MethodRun
import Lang.Proofs.LiveClosed
import Lang.Proofs.Receiver
import Lang.Proofs.Quote
import Lang.Proofs.StdRun

namespace Nanodregg.Lang.Std

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- The one-slot calls row, spelled out. -/
theorem callsT_one (t : Term) : callsT [t] = .record [("c0", t)] := rfl

/-- The generator's method names no closure package. -/
theorem noRef_generate (b : ByteArray) : NoRef (generateMethod b) := by
  simp [generateMethod, resultT, callsT_one, installT, someCallT, NoRef, NoRefRow]

/-- `generate` resolves at index 0 to its declared signature: the empty argument, one install slot,
no reads, no edits. -/
theorem generate_resolve {D : Type} (b : ByteArray) (doc : String) :
    resolveMethod (D := D) (generatorOf b doc) 0 = .ok ("generate", ⟨.record [], [installSlot], [], 0⟩) := rfl

/-- The generator's body is the one method. -/
theorem generator_body (b : ByteArray) (doc : String) :
    (generatorOf b doc).body = .record [("generate", generateMethod b)] := rfl

/-- The value `installT b` means: `some (install {pkg = b})`. -/
private theorem installT_bigStep {lib : List Term} {env : Env} {b : ByteArray} :
    BigStep lib env (installT b) (.ok (.inj "some" (.inj "install" (.record (suspend env [("pkg", .bytes b)]))))) :=
  .inj (.inj .record)

private theorem installT_means {lib : List Term} {env : Env} {b : ByteArray} :
    Means lib (optTy installSlot) (.inj "some" (.inj "install" (.record (suspend env [("pkg", .bytes b)]))))
      (.inj "some" (.inj "install" (.record [("pkg", .bytes b)]))) :=
  .inj rfl (.inj rfl (.record .record (.cons .bytes .bytes .nil)))

/-- **A generator's run returns its install.** For `generatorOf b doc` read at `pkg` with no imports
and no holes, every admitted run of method 0 returns the calls `[install b]` and no row acts. -/
theorem generate_run_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {b : ByteArray} {doc : String}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {args : ByteArray} {r : Req D}
    {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (generatorOf b doc))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state 0 args r budget = .ok (s, calls, rows, used)) :
    calls = [.install b] ∧ rows = [] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state 0 args r budget).map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state 0 args r budget with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, -, -, -, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  rw [generate_resolve] at hres
  cases hres
  simp only at hrun hx hes hc
  have hbig := run_bigStep hrun
  -- the receiver's application runs the method's body
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib
      [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal] (resultT (callsT [installT b]) (.var 2)) r' →
      BigStep L.lib [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal] (apply4 g "generate") r' :=
    fun hb => apply4_method hlib (generator_body b doc) (by simp [Row.find?, generateMethod]) (noRef_generate b) hb
  have hbody : BigStep L.lib [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal]
      (resultT (callsT [installT b]) (.var 2))
      (.ok (.record (suspend [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal]
        [("calls", callsT [installT b]), ("edits", .record []), ("state", .var 2)]))) := .record
  have hM := extract_means _ _ hx
  cases bigStep_deterministic hbig (fwd hbody)
  -- the calls field
  have hwC := BigStep.get (ℓ := "calls") (fwd hbody) (.field (find_suspend_of (t := callsT [installT b]) rfl) .record)
  obtain ⟨A, hA, hmC⟩ := means_get (fwd hbody) hM rfl hwC
  simp only [Row.find?] at hA
  cases hA
  have hC : Means L.lib (callsTy [installSlot])
      (.record (suspend [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal] [("c0", installT b)]))
      (.record [("c0", .inj "some" (.inj "install" (.record [("pkg", .bytes b)])))]) :=
    .record .record (.cons installT_bigStep installT_means .nil)
  have hcEq := means_deterministic hmC hC
  subst hcEq
  -- the edits field
  have hwE := BigStep.get (ℓ := "edits") (fwd hbody) (.field (find_suspend_of (t := .record []) rfl) .record)
  obtain ⟨A', hA', hmE⟩ := means_get (fwd hbody) hM rfl hwE
  simp only [Row.find?] at hA'
  cases hA'
  have hE : Means L.lib (.record []) (.record (suspend [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal] []))
      (.record []) := .record .record .nil
  have heEq := means_deterministic hmE hE
  subst heEq
  have hc' : callsOf digestOf [installSlot]
      (.record [("c0", .inj "some" (.inj "install" (.record [("pkg", .bytes b)])))]) = .ok [.install b] := rfl
  rw [hc'] at hc
  have he' : editsOf (D := D) (generatorOf b doc).rels r.self (.record []) = .ok [] := rfl
  rw [he'] at hes
  cases hc
  cases hes
  subst hrows
  exact ⟨rfl, rfl⟩


/-! ## Template generators: one theorem (LANG-88.1), two instances (LANG-87, LANG-88) -/

theorem templateGenerator_body (A : Ty) (ps : List Quote.Param) (p : Package) (doc : String) :
    (templateGenerator A ps p doc).body = .record [("generate", templateMethod A ps p)] := rfl

/-- A template method names no closure package when its parameters' terms name none. -/
theorem noRef_templateMethod {A : Ty} {ps : List Quote.Param} {p : Package} (hps : ∀ q ∈ ps, NoRef q.fetch) :
    NoRef (templateMethod A ps p) := by
  simp only [templateMethod, resultT, callsT_one, installOf, someCallT, NoRef, NoRefRow, and_true]
  exact Quote.noRef_quotePackage hps (by simp [NoRef]) _

/-- **A template generator's run installs its specification's bytes.** For `templateGenerator A ps p
doc` read at `pkg`, every admitted run of `generate` returns `[install B]` where `B` is
`encodePackage (fillPackage vals p)` — the template filled at the parameters' values — whenever
`generate` resolves to its declared signature (`hres`: a fact about `A` being data, decided by
`rfl` at any concrete `A`), the parameters mean those values in the method's environment (`Params`: `req` at `var 0`, the decoded
argument at `var 1`) and the filled package has bytes within a byte value (`bytesMax`, the honest
limit of staging at the byte level); and no row acts. -/
theorem generate_template_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {A : Ty} {ps : List Quote.Param} {p : Package} {doc : String} {vals : List Val}
    {B : ByteArray} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {args : ByteArray} {rq : Req D}
    {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (templateGenerator A ps p doc))
    (hres : resolveMethod (D := D) (templateGenerator A ps p doc) 0 = .ok ("generate", ⟨A, [installSlot], [], 0⟩))
    (hnoRef : ∀ q ∈ ps, NoRef q.fetch)
    (hparams : ∀ (lib : List Term) (ad sd wd : Data), Wire.decodeData A args = .ok ad →
      Quote.Params lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] ps vals)
    (hB : Wire.encodePackage (fillPackage vals p) = some B) (hsz : B.size ≤ Bounds.bytesMax)
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state 0 args rq budget = .ok (s, calls, rows, used)) :
    calls = [.install B] ∧ rows = [] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state 0 args rq budget).map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state 0 args rq budget with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p', ℓ, sg, sd, ad, wd, -, hl, hpg, hres', -, hdec, -, -, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f', hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  rw [hres] at hres'
  cases hres'
  simp only at hrun hx hes hc hdec
  have hbig := run_bigStep hrun
  have hps := hparams L.lib ad sd wd hdec
  -- the quoted term means the specification's bytes
  have hQ : BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] (Quote.quotePackage ps (.bytes .empty) p) (.ok (.bytes B)) := by
    have := Quote.quotePackage_sound hps hB (.bytes .empty) ByteArray.empty .bytes
      (by simpa [ByteArray.empty_append] using hsz)
    simpa [ByteArray.empty_append] using this
  -- the receiver's application runs the method's body
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
      (resultT (callsT [installOf (Quote.quotePackage ps (.bytes .empty) p)]) (.var 2)) r' →
      BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] (apply4 g "generate") r' :=
    fun hb => apply4_method (R := .record []) (S := genStateTy) (A := A) (Q := reqTy) hlib
      (templateGenerator_body A ps p doc) (by simp [Row.find?, templateMethod]) (noRef_templateMethod hnoRef) hb
  have hbody : BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] (resultT (callsT [installOf (Quote.quotePackage ps (.bytes .empty) p)]) (.var 2))
      (.ok (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
        [("calls", callsT [installOf (Quote.quotePackage ps (.bytes .empty) p)]), ("edits", .record []), ("state", .var 2)]))) :=
    .record
  have hM := extract_means _ _ hx
  cases bigStep_deterministic hbig (fwd hbody)
  -- the calls field
  have hwC := BigStep.get (ℓ := "calls") (fwd hbody)
    (.field (find_suspend_of (t := callsT [installOf (Quote.quotePackage ps (.bytes .empty) p)]) rfl) .record)
  obtain ⟨A', hA, hmC⟩ := means_get (fwd hbody) hM rfl hwC
  simp only [Row.find?] at hA
  cases hA
  have hBig : BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] (installOf (Quote.quotePackage ps (.bytes .empty) p))
      (.ok (.inj "some" (.inj "install" (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] [("pkg", Quote.quotePackage ps (.bytes .empty) p)]))))) :=
    .inj (.inj .record)
  have hMeans : Means L.lib (optTy installSlot)
      (.inj "some" (.inj "install" (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] [("pkg", Quote.quotePackage ps (.bytes .empty) p)]))))
      (.inj "some" (.inj "install" (.record [("pkg", .bytes B)]))) :=
    .inj rfl (.inj rfl (.record .record (.cons hQ .bytes .nil)))
  have hC : Means L.lib (callsTy [installSlot]) (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] [("c0", installOf (Quote.quotePackage ps (.bytes .empty) p))]))
      (.record [("c0", .inj "some" (.inj "install" (.record [("pkg", .bytes B)])))]) :=
    .record .record (.cons hBig hMeans .nil)
  have hcEq := means_deterministic hmC hC
  subst hcEq
  -- the edits field
  have hwE := BigStep.get (ℓ := "edits") (fwd hbody) (.field (find_suspend_of (t := .record []) rfl) .record)
  obtain ⟨A'', hA', hmE⟩ := means_get (fwd hbody) hM rfl hwE
  simp only [Row.find?] at hA'
  cases hA'
  have hE : Means L.lib (.record []) (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] [])) (.record []) := .record .record .nil
  have heEq := means_deterministic hmE hE
  subst heEq
  have hc' : callsOf digestOf [installSlot]
      (.record [("c0", .inj "some" (.inj "install" (.record [("pkg", .bytes B)])))]) = .ok [.install B] := rfl
  rw [hc'] at hc
  have he' : editsOf (D := D) (templateGenerator A ps p doc).rels rq.self (.record []) = .ok [] := rfl
  rw [he'] at hes
  cases hc
  cases hes
  subst hrows
  exact ⟨rfl, rfl⟩

/-! ## The bounded generator (LANG-87) -/

/-- A record of `get arg ℓ` fields is closed under four binders: filling changes nothing. -/
theorem fillFields_getArg (vals : List Val) : ∀ (r : List (Label × Ty)),
    Term.fillFields vals 4 (r.map fun (ℓ, _) => (ℓ, .get (.var 1) ℓ)) = r.map fun (ℓ, _) => (ℓ, .get (.var 1) ℓ)
  | [] => rfl
  | (ℓ, T) :: r => by simp [Term.fillFields, Term.fill, fillFields_getArg vals r]

/-- **The template at `max` is the Lean generator at `max`**: filling the one free variable of
`boundedPackageWith r f (var 4)` with the literal `max` gives `boundedPackage r f max`. -/
theorem fill_boundedPackage (r : List (Label × Ty)) (f : Label) (m : Nat) :
    fillPackage [.nat m] (boundedPackageWith r f (.var 4)) = boundedPackage r f m := by
  simp [fillPackage, boundedPackageWith, boundedPackage, boundedWith, lawOf, lawCase, lawCase6, allOf, guards,
    guard, okT, refusedT, At.newF, At.new, setMethod, resultT, callsT, natT, Term.fill, Term.fillFields,
    Val.lit?, fillFields_getArg]

/-- **The bounded generator's run installs its specification's bytes.** For `boundedGenerator r f`
read at `pkg`, every admitted run of `generate` whose argument decodes to `{max = m}` returns the
calls `[install B]` where `B` is `encodePackage (boundedPackage r f m)` — the Lean generator's
bytes at the receipt's argument — and no row acts. -/
theorem generate_bounded_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {r : List (Label × Ty)} {f : Label} {m : Nat} {B : ByteArray}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {args : ByteArray} {rq : Req D}
    {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (boundedGenerator r f))
    (hB : Wire.encodePackage (boundedPackage r f m) = some B) (hsz : B.size ≤ Bounds.bytesMax)
    (harg : Wire.decodeData maxArgTy args = .ok (.record [("max", .nat m)]))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state 0 args rq budget = .ok (s, calls, rows, used)) :
    calls = [.install B] ∧ rows = [] := by
  refine generate_template_sound bytesOf digestOf hid hp rfl ?_ ?_ (by rw [fill_boundedPackage]; exact hB) hsz h
  · intro q hq; simp only [List.mem_singleton] at hq; subst hq; simp [maxParam, NoRef]
  · intro lib ad sd wd hdec
    rw [harg] at hdec
    cases hdec
    have hmax : BigStep lib [(reqData bytesOf rq).toVal, (Data.record [("max", .nat m)]).toVal, sd.toVal, wd.toVal]
        (.get (.var 1) "max") (.ok (.nat m)) :=
      .get (.var rfl) (sel_toVal (d := .record [("max", .nat m)]) (x := .nat m) rfl)
    intro j
    cases j with
    | zero => exact ⟨hmax, trivial⟩
    | succ j => simp only [List.getElem?_cons_succ, List.getElem?_nil, Quote.ParamAt]

/-! ## The owner generator (LANG-88) -/

/-- The one-member allowlist is the template at that member. -/
theorem allowlistLaw_one (S : Ty) (i : ByteArray) : allowlistLaw S [i] = allowlistWith S (.digest i) := rfl

/-- **The template at a member is `ownedPackage` at that member.** -/
theorem fill_ownedPackage (r : List (Label × Ty)) (i : ByteArray) :
    fillPackage [.digest i] (ownedPackageWith r (.var 4)) = ownedPackage r i := by
  simp [fillPackage, ownedPackageWith, ownedPackage, allowlistWith, lawOf, lawCase, lawCase6, allOf, guards,
    guard, okT, refusedT, anyOf, At.reqF, At.req, setMethod, resultT, callsT, Term.fill, Term.fillFields,
    Val.lit?, fillFields_getArg]

/-- **The owner generator's run installs the allowlist of its invoker.** For `ownerGenerator r` read
at `pkg`, every admitted run of `generate` by the request `rq` returns `[install B]` where `B` is
`encodePackage (ownedPackage r (bytesOf rq.agent))`: the package names the SIGNER of the generating
Turn, and nobody else, by id — authority by naming, with the receipt as the only input. -/
theorem generate_owner_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {r : List (Label × Ty)} {B : ByteArray}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {args : ByteArray} {rq : Req D}
    {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (ownerGenerator r))
    (hB : Wire.encodePackage (ownedPackage r (bytesOf rq.agent)) = some B) (hsz : B.size ≤ Bounds.bytesMax)
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state 0 args rq budget = .ok (s, calls, rows, used)) :
    calls = [.install B] ∧ rows = [] := by
  refine generate_template_sound bytesOf digestOf hid hp rfl ?_ ?_ (by rw [fill_ownedPackage]; exact hB) hsz h
  · intro q hq; simp only [List.mem_singleton] at hq; subst hq; simp [agentParam, NoRef]
  · intro lib ad sd wd _
    have hagent : BigStep lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
        (.get (.var 0) "agent") (.ok (.digest (bytesOf rq.agent))) :=
      .get (.var rfl) (sel_toVal (d := reqData bytesOf rq) (x := .digest (bytesOf rq.agent)) rfl)
    intro j
    cases j with
    | zero => exact ⟨hagent, trivial⟩
    | succ j => simp only [List.getElem?_cons_succ, List.getElem?_nil, Quote.ParamAt]

/-! ## Template creators: generate AND instantiate in one Turn (LANG-96, KERNEL-77) -/

theorem templateCreator_body (A : Ty) (ps : List Quote.Param) (p : Package) (init : Term) (doc : String) :
    (templateCreator A ps p init doc).body = .record [("make", creatorMethod A ps p init)] := rfl

/-- A creator method names no closure package when its parameters' terms and its state term name
none. -/
theorem noRef_creatorMethod {A : Ty} {ps : List Quote.Param} {p : Package} {init : Term}
    (hps : ∀ q ∈ ps, NoRef q.fetch) (hi : NoRef init) : NoRef (creatorMethod A ps p init) := by
  simp only [creatorMethod, resultT, callsT_one, createOfT, someCallT, NoRef, NoRefRow, and_true]
  exact ⟨Quote.noRef_quotePackage hps (by simp [NoRef]) _, hi⟩

/-- **A template creator's run makes an object of its specification, owned by the invoker.** For
`templateCreator A ps p init doc` read at `pkg` (the template's state a record `row`), every admitted
run of `make` returns exactly `[createOf B [] S]`: `B` is `encodePackage (fillPackage vals p)`, the
template filled at the parameters' values (as `generate_template_sound`), and `S` the state slots of
the data `fs` that `init` means — whenever `make` resolves to its declared signature (`hres`, `rfl`
at a concrete argument and state type), the parameters mean `vals` and `init` means `fs` in the
method's environment, and the filled package has bytes within a byte value; no row acts. With
KERNEL-77's `createOf_parts` (the kernel's half) that is the receipt of "make me one at these
parameters": the Turn bore the signer's object of the package `B` installs as, at state `S`, and
the package cell too when the World lacked it, checked as any install is. -/
theorem make_template_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {A : Ty} {ps : List Quote.Param} {p : Package} {init : Term} {doc : String}
    {vals : List Val} {row : List (Label × Ty)} {fs : List (Label × Data)} {B : ByteArray} {S : Slots}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {args : ByteArray} {rq : Req D}
    {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (templateCreator A ps p init doc))
    (hrow : p.state = .record row)
    (hres : resolveMethod (D := D) (templateCreator A ps p init doc) 0 =
      .ok ("make", ⟨A, [createOfSlot p.state], [], 0⟩))
    (hnoRef : ∀ q ∈ ps, NoRef q.fetch) (hiRef : NoRef init)
    (hparams : ∀ (lib : List Term) (ad sd wd : Data), Wire.decodeData A args = .ok ad →
      Quote.Params lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] ps vals)
    (hinit : ∀ (lib : List Term) (ad sd wd : Data), Wire.decodeData A args = .ok ad →
      ∃ v, BigStep lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] init (.ok v) ∧
        Means lib p.state v (.record fs))
    (hB : Wire.encodePackage (fillPackage vals p) = some B) (hsz : B.size ≤ Bounds.bytesMax)
    (hS : stateSlots row fs 0 = some S)
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state 0 args rq budget = .ok (s, calls, rows, used)) :
    calls = [.createOf B [] S] ∧ rows = [] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state 0 args rq budget).map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state 0 args rq budget with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S', v, used, c, e, ds, left, es, hS', hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p', ℓ, sg, sd, ad, wd, -, hl, hpg, hres', -, hdec, -, -, rfl⟩ := runSetup_spec hS'
  obtain ⟨hpg', f', hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  rw [hres] at hres'
  cases hres'
  simp only at hrun hx hes hc hdec
  have hbig := run_bigStep hrun
  have hps := hparams L.lib ad sd wd hdec
  obtain ⟨vI, hI, hIM⟩ := hinit L.lib ad sd wd hdec
  have hQ : BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] (Quote.quotePackage ps (.bytes .empty) p) (.ok (.bytes B)) := by
    have := Quote.quotePackage_sound hps hB (.bytes .empty) ByteArray.empty .bytes
      (by simpa [ByteArray.empty_append] using hsz)
    simpa [ByteArray.empty_append] using this
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
      (resultT (callsT [createOfT p.state (Quote.quotePackage ps (.bytes .empty) p) init]) (.var 2)) r' →
      BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] (apply4 g "make") r' :=
    fun hb => apply4_method (R := .record []) (S := genStateTy) (A := A) (Q := reqTy) hlib
      (templateCreator_body A ps p init doc) (by simp [Row.find?, creatorMethod]) (noRef_creatorMethod hnoRef hiRef) hb
  have hbody : BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
      (resultT (callsT [createOfT p.state (Quote.quotePackage ps (.bytes .empty) p) init]) (.var 2))
      (.ok (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
        [("calls", callsT [createOfT p.state (Quote.quotePackage ps (.bytes .empty) p) init]), ("edits", .record []),
          ("state", .var 2)]))) :=
    .record
  have hM := extract_means _ _ hx
  cases bigStep_deterministic hbig (fwd hbody)
  -- the calls field
  have hwC := BigStep.get (ℓ := "calls") (fwd hbody)
    (.field (find_suspend_of (t := callsT [createOfT p.state (Quote.quotePackage ps (.bytes .empty) p) init]) rfl) .record)
  obtain ⟨A', hA, hmC⟩ := means_get (fwd hbody) hM rfl hwC
  simp only [Row.find?] at hA
  cases hA
  have hBig : BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
      (createOfT p.state (Quote.quotePackage ps (.bytes .empty) p) init)
      (.ok (.inj "some" (.inj "createOf" (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
        [("pkg", Quote.quotePackage ps (.bytes .empty) p), ("state", init)]))))) :=
    .inj (.inj .record)
  have hMeans : Means L.lib (optTy (createOfSlot p.state))
      (.inj "some" (.inj "createOf" (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
        [("pkg", Quote.quotePackage ps (.bytes .empty) p), ("state", init)]))))
      (.inj "some" (.inj "createOf" (.record [("pkg", .bytes B), ("state", .record fs)]))) :=
    .inj rfl (.inj rfl (.record .record (.cons hQ .bytes (.cons hI hIM .nil))))
  have hC : Means L.lib (callsTy [createOfSlot p.state])
      (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal]
        [("c0", createOfT p.state (Quote.quotePackage ps (.bytes .empty) p) init)]))
      (.record [("c0", .inj "some" (.inj "createOf" (.record [("pkg", .bytes B), ("state", .record fs)])))]) :=
    .record .record (.cons hBig hMeans .nil)
  have hcEq := means_deterministic hmC hC
  subst hcEq
  -- the edits field
  have hwE := BigStep.get (ℓ := "edits") (fwd hbody) (.field (find_suspend_of (t := .record []) rfl) .record)
  obtain ⟨A'', hA', hmE⟩ := means_get (fwd hbody) hM rfl hwE
  simp only [Row.find?] at hA'
  cases hA'
  have hE : Means L.lib (.record []) (.record (suspend [(reqData bytesOf rq).toVal, ad.toVal, sd.toVal, wd.toVal] []))
      (.record []) := .record .record .nil
  have heEq := means_deterministic hmE hE
  subst heEq
  have hst : slotCreateState (createOfSlot (.record row)) = some (.record row) := rfl
  have hc' : callsOf digestOf [createOfSlot p.state]
      (.record [("c0", .inj "some" (.inj "createOf" (.record [("pkg", .bytes B), ("state", .record fs)])))]) =
        .ok [.createOf B [] S] := by
    simp [callsOf, callsOf.go, bodyOf, hst, hrow, stateBytes, hS, bind, Except.bind, pure, Except.pure, Except.map]
  rw [hc'] at hc
  have he' : editsOf (D := D) (templateCreator A ps p init doc).rels rq.self (.record []) = .ok [] := rfl
  rw [he'] at hes
  cases hc
  cases hes
  subst hrows
  exact ⟨rfl, rfl⟩

/-- `make` resolves to its declared signature at the deployed label (`hres` of `make_bounded_sound`:
the slot's state type is checked by computation, which a variable label stops). -/
theorem boundedCreator_resolve {D : Type} (k : Nat) :
    resolveMethod (D := D) (boundedCreator "n" k) 0 =
      .ok ("make", ⟨maxArgTy, [createOfSlot (.record [("n", .nat)])], [], 0⟩) := rfl

/-- **The bounded creator's run makes its invoker an object of the Lean generator's package.** For
`boundedCreator f k` read at `pkg`, every admitted run of `make` whose argument decodes to
`{max = m}` returns `[createOf B [] S]` where `B` is `encodePackage (boundedPackage {f : nat} f m)`
— the bytes `generate_bounded_sound` names at the same argument — and `S` is the state `{f = k}`; no
row acts. -/
theorem make_bounded_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {f : Label} {k m : Nat} {B : ByteArray} {S : Slots}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {args : ByteArray} {rq : Req D}
    {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (boundedCreator f k))
    (hres : resolveMethod (D := D) (boundedCreator f k) 0 =
      .ok ("make", ⟨maxArgTy, [createOfSlot (.record [(f, .nat)])], [], 0⟩))
    (hB : Wire.encodePackage (boundedPackage [(f, .nat)] f m) = some B) (hsz : B.size ≤ Bounds.bytesMax)
    (hS : stateSlots [(f, .nat)] [(f, .nat k)] 0 = some S)
    (harg : Wire.decodeData maxArgTy args = .ok (.record [("max", .nat m)]))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state 0 args rq budget = .ok (s, calls, rows, used)) :
    calls = [.createOf B [] S] ∧ rows = [] := by
  refine make_template_sound bytesOf digestOf (row := [(f, .nat)]) (fs := [(f, .nat k)]) hid hp rfl hres ?_
    (by simp [natT, NoRef, NoRefRow]) ?_ ?_ (by rw [fill_boundedPackage]; exact hB) hsz hS h
  · intro q hq; simp only [List.mem_singleton] at hq; subst hq; simp [maxParam, NoRef]
  · intro lib ad sd wd hdec
    rw [harg] at hdec
    cases hdec
    have hmax : BigStep lib [(reqData bytesOf rq).toVal, (Data.record [("max", .nat m)]).toVal, sd.toVal, wd.toVal]
        (.get (.var 1) "max") (.ok (.nat m)) :=
      .get (.var rfl) (sel_toVal (d := .record [("max", .nat m)]) (x := .nat m) rfl)
    intro j
    cases j with
    | zero => exact ⟨hmax, trivial⟩
    | succ j => simp only [List.getElem?_cons_succ, List.getElem?_nil, Quote.ParamAt]
  · intro lib ad sd wd _
    exact ⟨_, .record, .record .record (.cons .nat .nat .nil)⟩

/-! ## The quorum generator (LANG-99): an install only on a commit -/

theorem quorumGenerator_body (r : List (Label × Ty)) (f : Label) (members : List ByteArray) (k : Nat) :
    (quorumGenerator r f members k).body = .record [("approve", approveGenMethod),
      ("generate", quorumGenerateMethod (boundedPackageWith r f (.var 4))),
      ("propose", proposeGenMethod), ("quorum", quorumLaw quorumGenStateTy .nat members k "generated")] := rfl

theorem noRef_quorumGenerate (p : Package) : NoRef (quorumGenerateMethod p) := by
  have hq := Quote.noRef_quotePackage (ps := [⟨.nat, .var 0⟩]) (buf := .bytes .empty) (by simp [NoRef]) (by simp [NoRef]) p
  simp only [quorumGenerateMethod, resultT, callsT_one, installOf, someCallT, NoRef, NoRefRow, natT, hq,
    and_self]

/-- **A quorum generator installs only the approved proposal, and only as it commits it.** For
`quorumGenerator r f members k` read at `pkg`, every admitted run of `generate` (method 1) read the
object's state as `{approvals = a, generated = g, proposal = set v}` with `v ≠ g`, and returns
exactly `[install B]` with `B` = `encodePackage (boundedPackage r f v)` — the bounded package at the
PROPOSED bound — and no row acts. Its new state is `{approvals = 0, generated = v, …}`, a change of
`generated` that the quorum law in force judges as a commit (k approvals of exactly `set v`); the
kernel judges the laws before deriving the install (`invoke_ok`), and the Turn fails whole. The
hypotheses: `generate` resolves to its signature (`rfl` at a concrete label), and the template has
bytes within a byte value at every bound (it does: a bound is a fixed-width `u64` literal). -/
theorem generate_quorum_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {r : List (Label × Ty)} {f : Label} {members : List ByteArray} {k : Nat}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {args : ByteArray} {rq : Req D}
    {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (quorumGenerator r f members k))
    (hres : resolveMethod (D := D) (quorumGenerator r f members k) 1 =
      .ok ("generate", ⟨.record [], [installSlot], [], 0⟩))
    (hB : ∀ m, ∃ B, Wire.encodePackage (boundedPackage r f m) = some B ∧ B.size ≤ Bounds.bytesMax)
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state 1 args rq budget = .ok (s, calls, rows, used)) :
    ∃ a g v B, readState digestOf quorumGenRow state =
        .ok (.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj "set" (.nat v))]) ∧
      v ≠ g ∧ Wire.encodePackage (boundedPackage r f v) = some B ∧ calls = [.install B] ∧ rows = [] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state 1 args rq budget).map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state 1 args rq budget with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v0, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g0, p', ℓ, sg, sd, ad, wd, -, hl, hpg, hres', hst, -, -, -, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f', hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  rw [hres] at hres'
  cases hres'
  simp only at hrun hx hes hc hst
  have hbig := run_bigStep hrun
  -- the state the run read: three fields, the proposal one of two arms
  have hconf := readState_conforms hst
  cases hconf with | record hr => cases hr with | cons h1 hr => cases hr with | cons h2 hr =>
  cases hr with | cons h3 hr =>
  cases hr
  obtain ⟨a, rfl⟩ := conf_nat h1
  obtain ⟨g, rfl⟩ := conf_nat h2
  cases h3 with | inj hfp hpd =>
  rename_i ℓp A pd
  have env_state : ∀ {r' : Except Fault Val}, BigStep L.lib
      [(reqData bytesOf rq).toVal, ad.toVal,
        (Data.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj ℓp pd)]).toVal, wd.toVal]
      (.case (.get (.var 2) "proposal")
        [("laws", .refuse quorumGenResultTy "notSet".toUTF8),
         ("set", .ite (.prim .eq (.var 0) (.get (.var 3) "generated")) (.refuse quorumGenResultTy "notProposed".toUTF8)
            (resultT (callsT [installOf (Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty) (boundedPackageWith r f (.var 4)))])
              (.record [("approvals", natT 0), ("generated", .var 0), ("proposal", .get (.var 3) "proposal")])))]) r' →
      BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal,
        (Data.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj ℓp pd)]).toVal, wd.toVal]
        (apply4 g0 "generate") r' :=
    fun hb => apply4_method (R := .record []) (S := quorumGenStateTy) (A := .record []) (Q := reqTy) hlib
      (quorumGenerator_body r f members k) (by simp [Row.find?, quorumGenerateMethod])
      (noRef_quorumGenerate _) hb
  have hprop : BigStep L.lib [(reqData bytesOf rq).toVal, ad.toVal,
      (Data.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj ℓp pd)]).toVal, wd.toVal]
      (.get (.var 2) "proposal") (.ok (.inj ℓp pd.toVal)) :=
    .get (.var rfl) (sel_toVal (d := .record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj ℓp pd)])
      (x := .inj ℓp pd) rfl)
  simp only [Row.find?] at hfp
  split at hfp
  · -- `laws`: the run is refused `notSet`, never admitted
    rename_i hl'
    subst hl'
    have := env_state (.case hprop rfl .refuse)
    cases bigStep_deterministic hbig this
  split at hfp
  · rename_i hs'
    subst hs'
    cases hfp
    obtain ⟨v, rfl⟩ := conf_nat hpd
    have hgen : BigStep L.lib [(Data.nat v).toVal, (reqData bytesOf rq).toVal, ad.toVal,
        (Data.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj "set" (.nat v))]).toVal, wd.toVal]
        (.get (.var 3) "generated") (.ok (.nat g)) :=
      .get (.var rfl) (sel_toVal (d := .record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj "set" (.nat v))])
        (x := .nat g) rfl)
    have hcond : BigStep L.lib [(Data.nat v).toVal, (reqData bytesOf rq).toVal, ad.toVal,
        (Data.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj "set" (.nat v))]).toVal, wd.toVal]
        (.prim .eq (.var 0) (.get (.var 3) "generated")) (.ok (.bool (decide (v = g)))) :=
      BigStep.prim (p := .eq) (x := .nat v) (y := .nat g) (.var rfl) hgen (by simp [primEval])
    by_cases hvg : v = g
    · -- `v = generated`: refused `notProposed`
      subst hvg
      have := env_state (.case hprop rfl (.iteT (by simpa using hcond) .refuse))
      cases bigStep_deterministic hbig this
    · obtain ⟨B, hBv, hsz⟩ := hB v
      refine ⟨a, g, v, B, hst, hvg, hBv, ?_⟩
      have hcondF : BigStep L.lib [(Data.nat v).toVal, (reqData bytesOf rq).toVal, ad.toVal,
          (Data.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj "set" (.nat v))]).toVal, wd.toVal]
          (.prim .eq (.var 0) (.get (.var 3) "generated")) (.ok (.bool false)) := by simpa [hvg] using hcond
      let env' := [(Data.nat v).toVal, (reqData bytesOf rq).toVal, ad.toVal,
        (Data.record [("approvals", .nat a), ("generated", .nat g), ("proposal", .inj "set" (.nat v))]).toVal, wd.toVal]
      have hps : ∀ lib, Quote.Params lib env' [⟨.nat, .var 0⟩] [.nat v] := by
        intro lib j
        cases j with
        | zero => exact ⟨.var rfl, trivial⟩
        | succ j => simp only [List.getElem?_cons_succ, List.getElem?_nil, Quote.ParamAt]
      have hQ : BigStep L.lib env' (Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty) (boundedPackageWith r f (.var 4)))
          (.ok (.bytes B)) := by
        have := Quote.quotePackage_sound (hps L.lib) (by rw [fill_boundedPackage]; exact hBv) (.bytes .empty)
          ByteArray.empty .bytes (by simpa [ByteArray.empty_append] using hsz)
        simpa [ByteArray.empty_append] using this
      have hbody : BigStep L.lib env'
          (resultT (callsT [installOf (Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty) (boundedPackageWith r f (.var 4)))])
            (.record [("approvals", natT 0), ("generated", .var 0), ("proposal", .get (.var 3) "proposal")]))
          (.ok (.record (suspend env'
            [("calls", callsT [installOf (Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty) (boundedPackageWith r f (.var 4)))]),
             ("edits", .record []),
             ("state", .record [("approvals", natT 0), ("generated", .var 0), ("proposal", .get (.var 3) "proposal")])]))) :=
        .record
      have hrun' := env_state (.case hprop rfl (.iteF hcondF hbody))
      cases bigStep_deterministic hbig hrun'
      have hM := extract_means _ _ hx
      -- the calls field
      have hwC := BigStep.get (ℓ := "calls") hrun'
        (.field (find_suspend_of (t := callsT [installOf (Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty)
          (boundedPackageWith r f (.var 4)))]) rfl) .record)
      obtain ⟨A', hA, hmC⟩ := means_get hrun' hM rfl hwC
      simp only [Row.find?] at hA
      cases hA
      have hMeans : Means L.lib (optTy installSlot)
          (.inj "some" (.inj "install" (.record (suspend env'
            [("pkg", Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty) (boundedPackageWith r f (.var 4)))]))))
          (.inj "some" (.inj "install" (.record [("pkg", .bytes B)]))) :=
        .inj rfl (.inj rfl (.record .record (.cons hQ .bytes .nil)))
      have hC : Means L.lib (callsTy [installSlot])
          (.record (suspend env' [("c0", installOf (Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty)
            (boundedPackageWith r f (.var 4))))]))
          (.record [("c0", .inj "some" (.inj "install" (.record [("pkg", .bytes B)])))]) :=
        .record .record (.cons (.inj (.inj .record)) hMeans .nil)
      have hcEq := means_deterministic hmC hC
      subst hcEq
      -- the edits field
      have hwE := BigStep.get (ℓ := "edits") hrun' (.field (find_suspend_of (t := .record []) rfl) .record)
      obtain ⟨A'', hA', hmE⟩ := means_get hrun' hM rfl hwE
      simp only [Row.find?] at hA'
      cases hA'
      have hE : Means L.lib (.record []) (.record (suspend env' [])) (.record []) := .record .record .nil
      have heEq := means_deterministic hmE hE
      subst heEq
      have hc' : callsOf digestOf [installSlot]
          (.record [("c0", .inj "some" (.inj "install" (.record [("pkg", .bytes B)])))]) = .ok [.install B] := rfl
      rw [hc'] at hc
      have he' : editsOf (D := D) (quorumGenerator r f members k).rels rq.self (.record []) = .ok [] := rfl
      rw [he'] at hes
      cases hc
      cases hes
      subst hrows
      exact ⟨rfl, rfl⟩
  · cases hfp

end Nanodregg.Lang.Std
