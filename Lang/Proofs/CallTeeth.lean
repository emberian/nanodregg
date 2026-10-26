/-
# Lang.Proofs.CallTeeth — `callsOf` on concrete rows, and the round trip's premise is satisfiable

Over `D = ByteArray` with an 8-byte digest (the Sim's width): `none` slots are skipped wherever they
sit, a slot that names a cell by non-digest bytes refuses the run with the slot and field by name,
an invoke's `args` leave as the BYTES of the value the method returned (`callsOf_encodes`, LANG-77),
a slot without an invoke arm holding an invoke datum is refused by name (`callsOf_no_arm`: typing
keeps it from a checked run), a grant with five rights has no call data, and `bodyOf_callData`'s
premise holds for the identity digest (`bodyOf_callData_bytes`), so the round trip is not vacuous.
At install: an `invoke`-only slot carrying an invoke checks; a slot arm with the right label at
the wrong type, an empty sum, and an invoke arm at a function type (`slot_fn_arg`, LANG-77) are
refused `badMethod`; a transfer in an `invoke`-only slot is `illTyped`. Liveness
(`Lang.Proofs.CallLive`): its premises are met by a real calls row (`invokeRow_conforms`), the
non-digest refusal above is the one it allows (`not_digest_is_live`), and a refusal naming a field
that holds no digest, a nat (`method`) or the argument record (`args`), is not
(`method_named_not_live`, `args_named_not_live`). A call read from an invoke-only slot is an
invoke (`skip_none_kind`), and the Sim's digest codec meets `bodyOf_callData`'s premise
(`sim_digest_roundtrip`, `bodyOf_callData_sim`).
-/
import Lang.Proofs.Call
import Lang.Proofs.CallLive
import Kernel.Sim

namespace Nanodregg.Lang.Teeth

open Nanodregg.Kernel.Receive

private def dig8 (b : ByteArray) : Option ByteArray := if b.size = 8 then some b else none

private def obj8 : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩

/-- The empty argument type: what these invokes send. -/
private def UA : Ty := .record []

/-- An invoke-only slot whose argument is the empty record. -/
private def invokeSlot : Ty := invokeOf UA

private def invokeD (obj : ByteArray) : Data :=
  .inj "invoke" (.record [("args", .record []), ("budget", .nat 10), ("method", .nat 0),
    ("obj", .digest obj), ("via", .inj "none" (.record []))])

/-- The bytes of the empty record at `UA`: none. -/
private def unitBytes : ByteArray := (Wire.encodeData UA (.record [])).getD ⟨#[7]⟩

private def callsIs (e : Except (Refusal ByteArray) (List (Body ByteArray))) (bs : List (Body ByteArray)) : Bool :=
  match e with
  | .ok bs' => decide (bs' = bs)
  | .error _ => false

private def refusedWith (e : Except (Refusal ByteArray) (List (Body ByteArray))) (why : String) : Bool :=
  match e with
  | .error (.program w) => w == why
  | _ => false

/-- An empty slot before a call is skipped: the call is the only Body, its `args` the bytes of the
empty record. -/
theorem callsOf_skips_none :
    callsIs (callsOf dig8 [invokeSlot, invokeSlot]
      (.record [("c0", .inj "none" (.record [])), ("c1", .inj "some" (invokeD obj8))]))
      [.invoke obj8 0 unitBytes 10 none] = true := by decide +kernel

/-- **The runtime encodes a composed argument** (LANG-77): an invoke whose slot carries a natural
leaves with the bytes of the natural the method returned, the bytes the callee's `decodeData .nat`
reads back. -/
theorem callsOf_encodes :
    callsIs (callsOf dig8 [invokeOf .nat]
      (.record [("c0", .inj "some" (.inj "invoke" (.record [("args", .nat 4), ("budget", .nat 10),
        ("method", .nat 0), ("obj", .digest obj8), ("via", .inj "none" (.record []))])))]))
      [.invoke obj8 0 ((Wire.encodeData .nat (.nat 4)).getD ⟨#[7]⟩) 10 none] = true := by decide +kernel

/-- A slot with no invoke arm holding an invoke datum is refused by name (never from a checked run:
the slot's type has no such arm). -/
theorem callsOf_no_arm :
    refusedWith (callsOf dig8 [callOf ["transfer"]] (.record [("c0", .inj "some" (invokeD obj8))]))
      "calls: c0 args: no invoke arm" = true := by decide +kernel

/-- A call naming its object by three bytes is refused by slot and field. -/
theorem callsOf_not_digest :
    refusedWith (callsOf dig8 [invokeSlot] (.record [("c0", .inj "some" (invokeD ⟨#[120, 121, 122]⟩))]))
      "calls: c0 obj: not a digest" = true := by decide +kernel

/-- A slot that is not an option is refused by name. -/
theorem callsOf_not_option :
    refusedWith (callsOf dig8 [invokeSlot] (.record [("c0", .nat 3)])) "calls: c0: not an option" = true := by
  decide +kernel

/-- A grant carrying more rights than `rightsMax` has no call data. -/
theorem callData_five_rights :
    callData id none (Body.grant obj8 obj8 [.observe, .mutate, .invoke 0, .invoke 1, .enroll 2] none) = none := by
  decide +kernel

/-- The same grant at four rights has call data. -/
theorem callData_four_rights :
    (callData id none (Body.grant obj8 obj8 [.observe, .mutate, .invoke 0, .enroll 2] none)).isSome = true := by
  decide +kernel

/-- `bodyOf_callData` at the identity digest: its premise is satisfiable. -/
theorem bodyOf_callData_bytes {A : Option Ty} {b : Body ByteArray} {d : Data} (h : callData id A b = some d) :
    bodyOf some A d = .ok b :=
  bodyOf_callData (fun _ => rfl) h

/-! ## Call slots at install: the slot's type is checked against the call arms, the body against the slot -/

private def S1 : Ty := .record [("n", .nat)]

/-- A one-method package whose method has call slots `ks` and body `go`. -/
private def slotPkg (ks : List Ty) (go : Term) : Package :=
  { imports := [], state := S1, iface := .record [("go", methodTy S1 (.record []) ks)],
    body := .record [("go", go)], methods := ["go"], laws := [] }

private def invokeOnly : Ty := invokeOf UA

private def isOkC : Except CheckError Unit → Bool
  | .ok () => true
  | .error _ => false

private def isBadMethod : Except CheckError Unit → Bool
  | .error (.badMethod "go") => true
  | _ => false

private def isIllTyped : Except CheckError Unit → Bool
  | .error (.illTyped _) => true
  | _ => false

/-- `λ rows s a r. {calls = {c0 = slot}, edits = {}, state = s}` -/
private def goWith (slot : Term) : Term :=
  .lam (.record []) (.lam S1 (.lam (.record []) (.lam reqTy (resultT (callsT [slot]) (.var 2)))))

/-- An `invoke` call of call type `T`, its argument the empty record. -/
private def anInvoke (T : Ty) : Term :=
  .inj T "invoke" (.record [("args", .record []), ("budget", .nat 1), ("method", .nat 0),
    ("obj", .digest .empty), ("via", .inj (optTy .digest) "none" (.record []))])

/-- The control: an invoke-only slot carrying an invoke installs. -/
theorem slot_invoke_checks : isOkC ((slotPkg [invokeOnly] (goWith (someCallT invokeOnly (anInvoke invokeOnly)))).checkWith []) = true := by
  decide +kernel

/-- A slot whose `invoke` arm has the right label but `budget : bytes` is not a call slot: the
method's type is refused `badMethod`. -/
theorem slot_wrong_arm_type :
    let bad : Ty := .sum [("invoke", .record [("args", UA), ("budget", .bytes), ("method", .nat),
      ("obj", .digest), ("via", optTy .digest)])]
    isBadMethod ((slotPkg [bad] (goWith (noCallT bad))).checkWith []) = true := by
  decide +kernel

/-- A slot over the empty sum (which could never hold a call) is refused `badMethod`. -/
theorem slot_empty_sum :
    isBadMethod ((slotPkg [.sum []] (goWith (noCallT (.sum [])))).checkWith []) = true := by
  decide +kernel

/-- A slot naming only `invoke` without an argument type (`callOf ["invoke"]`) is the empty sum:
refused `badMethod` (LANG-77: the old spelling refuses to load). -/
theorem slot_bare_invoke :
    isBadMethod ((slotPkg [callOf ["invoke"]] (goWith (noCallT (callOf ["invoke"])))).checkWith []) = true := by
  decide +kernel

/-- An invoke arm whose argument is a FUNCTION type: no value of it has bytes, so the slot is not a
call slot and the method is refused `badMethod` (LANG-77; journey LC7). -/
theorem slot_fn_arg :
    isBadMethod ((slotPkg [invokeOf (.fn .nat .nat)] (goWith (noCallT (invokeOf (.fn .nat .nat))))).checkWith []) = true := by
  decide +kernel

/-- An invoke-only slot carrying a transfer does not check: `illTyped`. -/
theorem slot_kind_outside :
    let tr : Term := .inj invokeOnly "transfer" (.record [("amount", .nat 1),
      ("dst", .inj acctRefTy "well" (.digest .empty)), ("once", .inj (optTy .bytes) "none" (.record [])),
      ("src", .inj acctRefTy "well" (.digest .empty)), ("via", .inj (optTy .digest) "none" (.record []))])
    isIllTyped ((slotPkg [invokeOnly] (goWith (someCallT invokeOnly tr))).checkWith []) = true := by
  decide +kernel

/-- An `install` datum in an install-only slot reads as `.install` of its bytes (LANG-86), so a
generator's one call reaches the kernel as the install it is. -/
theorem install_reads :
    callsIs (callsOf dig8 [callOf ["install"]]
      (.record [("c0", .inj "some" (.inj "install" (.record [("pkg", .bytes obj8)])))])) [.install obj8] = true := by
  decide +kernel

/-! ## Liveness: its premises are met, and the refusal it allows is the real one -/

theorem invokeSlot_ok : callSlotOk invokeSlot = true := by decide

/-- The slot, as the sum it is. -/
private theorem invokeSlot_eq : invokeSlot = .sum [("invoke", invokeArm UA)] := by decide

theorem invokeD_conforms (obj : ByteArray) (h : obj.size ≤ Bounds.digestBytesMax) : Conforms (invokeD obj) invokeSlot := by
  rw [invokeSlot_eq]
  exact .inj rfl (.record (.cons (.record .nil) (.cons (.nat (by decide)) (.cons (.nat (by decide))
    (.cons (.digest h) (.cons (.inj (A := .record []) rfl (.record .nil)) .nil))))))

/-- A one-slot calls row holding an invoke conforms to `callsTy [invoke-only]`. -/
theorem invokeRow_conforms (obj : ByteArray) (h : obj.size ≤ Bounds.digestBytesMax) :
    Conforms (.record [("c0", .inj "some" (invokeD obj))]) (callsTy [invokeSlot]) :=
  .record (.cons (.inj (A := invokeSlot) rfl (invokeD_conforms obj h)) .nil)

/-- `callsOf_not_digest`'s refusal is the one `callsOf_live` allows: bytes the digest refuses. -/
theorem not_digest_is_live :
    ∀ e, callsOf dig8 [invokeSlot] (.record [("c0", .inj "some" (invokeD ⟨#[120, 121, 122]⟩))]) = .error e →
      DigestRefusal dig8 (.record [("c0", .inj "some" (invokeD ⟨#[120, 121, 122]⟩))]) e :=
  callsOf_live (by simp [invokeSlot_ok]) (invokeRow_conforms _ (by decide))

/-- The refusal's text fixes the name it gives: `calls: c0 F: not a digest` names `F`. -/
theorem c0_named {f g : String} (h : s!"calls: c0 {f}: not a digest" = s!"calls: c0 {g}: not a digest") : f = g := by
  have h1 := congrArg String.toList h
  have h2 : f.toList ++ ": not a digest".toList = g.toList ++ ": not a digest".toList := by
    simpa [toString] using h1
  exact String.toList_inj.mp (List.append_cancel_right h2)

/-- A name with no `.` names a path of one label: itself. -/
theorem names_one {p : List Label} {f : String} (h : Names p f) (hf : '.' ∉ f.toList) : p = [f] := by
  cases h with
  | one => rfl
  | cons ℓ h' => exact (hf (by simp)).elim

/-- The row's `method` field is a nat: no bytes sit at path `c0.method`. -/
theorem no_bytes_at_method {b : ByteArray} {q : List Label}
    (hb : DigestAt b q (.inj "some" (invokeD ⟨#[120, 121, 122]⟩))) (hq : q = ["method"]) : False := by
  simp only [invokeD] at hb
  cases hb with
  | arm _ => simp at hq
  | inj hb =>
    cases hb with
    | arm _ => simp at hq
    | inj hb =>
      cases hb with
      | field hm hb =>
        simp only [List.cons.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        simp at hm
        subst hm
        cases hb

/-- **A refusal names the field that holds the refused bytes** (cv 01a14a69-5909). The row holds
bytes that `dig8` refuses (`obj` is 3 bytes), yet a refusal that names the slot's `method` field, a
nat, is not one `callsOf_live` allows. Under the old `BytesIn`, any bytes leaf witnessed any name,
and this was a `DigestRefusal`. -/
theorem method_named_not_live :
    ¬ DigestRefusal dig8 (.record [("c0", .inj "some" (invokeD ⟨#[120, 121, 122]⟩))])
      (.program "calls: c0 method: not a digest") := by
  rintro ⟨ℓ, p, f, b, -, hb, hn, he⟩
  cases hb with
  | field hm hb =>
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp only [Refusal.program.injEq] at he
    have hf : f = "method" := c0_named (g := "method") he.symm
    subst hf
    exact no_bytes_at_method hb (names_one hn (by decide))

/-- The row's `args` field is the empty record, never a digest: no digest leaf sits at path
`c0.args`. -/
theorem no_digest_at_args {b : ByteArray} {q : List Label}
    (hb : DigestAt b q (.inj "some" (invokeD ⟨#[120, 121, 122]⟩))) (hq : q = ["args"]) : False := by
  simp only [invokeD] at hb
  cases hb with
  | arm _ => simp at hq
  | inj hb =>
    cases hb with
    | arm _ => simp at hq
    | inj hb =>
      cases hb with
      | field hm hb =>
        simp only [List.cons.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        simp at hm
        subst hm
        cases hb

/-- **Only a digest field is refused as not a digest** (cv 01a14aab-adae, LANG-38). A refusal
naming `args`, a value of the slot's argument type (LANG-77: here the empty record), is not one
`callsOf_live` allows. -/
theorem args_named_not_live :
    ¬ DigestRefusal dig8 (.record [("c0", .inj "some" (invokeD ⟨#[120, 121, 122]⟩))])
      (.program "calls: c0 args: not a digest") := by
  rintro ⟨ℓ, p, f, b, -, hb, hn, he⟩
  cases hb with
  | field hm hb =>
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp only [Refusal.program.injEq] at he
    have hf : f = "args" := c0_named (g := "args") he.symm
    subst hf
    exact no_digest_at_args hb (names_one hn (by decide))

/-- A call read from an invoke-only slot is an invoke, the row's one call. -/
theorem skip_none_kind {bs : List (Body ByteArray)}
    (h : callsOf dig8 [invokeSlot] (.record [("c0", .inj "some" (invokeD obj8))]) = .ok bs) :
    ∀ b ∈ bs, b.kindName = "invoke" := by
  have hc := invokeRow_conforms obj8 (by decide)
  cases hc with
  | record hrow =>
    obtain ⟨ts, hts, hf⟩ := callsOf_go_kinds (by simp [slotLabels]) hrow (by simp [invokeSlot_ok])
      (by simpa [callsOf] using h)
    intro b hb
    obtain ⟨t, ht, arms, hta, hk⟩ := hf.mem_left b hb
    have htm := hts.subset ht
    simp only [slotLabels, List.range, List.range.loop, List.map, List.zip, List.zipWith, List.mem_cons,
      List.not_mem_nil, or_false] at htm
    subst htm
    rw [invokeSlot_eq] at hta
    simp only [optTy, Ty.sum.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hta
    subst hta
    simpa using hk

/-- The Sim's digest codec (`u64`, little-endian) reads back what it writes: `bodyOf_callData`'s
premise at the deployed toy parameters. -/
theorem sim_digest_roundtrip (x : Kernel.Sim.D) : Kernel.Sim.digestOf (Kernel.Sim.dc.bytes x) = some x := by
  unfold Kernel.Sim.digestOf Kernel.Sim.dc
  rw [Codec.Stream.decode_bytes Codec.Stream.u64_lawful]

theorem bodyOf_callData_sim {A : Option Ty} {b : Body Kernel.Sim.D} {d : Data}
    (h : callData Kernel.Sim.dc.bytes A b = some d) : bodyOf Kernel.Sim.digestOf A d = .ok b :=
  bodyOf_callData sim_digest_roundtrip h

end Nanodregg.Lang.Teeth
