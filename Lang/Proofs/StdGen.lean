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

end Nanodregg.Lang.Std
