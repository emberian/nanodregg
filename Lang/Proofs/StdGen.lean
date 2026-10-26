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
theorem generate_run_sound {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
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

end Nanodregg.Lang.Std
