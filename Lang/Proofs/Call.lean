/-
# Lang.Proofs.Call — the calls a method returns are exactly KERNEL's callable Bodies

* `bodyOf_callable`, `callsOf_callable`: every Body `callsOf` reads is of a kind an object may
  exercise; `callsOf_length`: no more calls than slots; `extract_result_calls`: the calls row of
  a method's extracted result has its declared slots, and `resolveMethod_slots`: at most
  `Kernel.Bounds.callsMax` of them. `runMeasured_calls_slots`: a run makes at most the resolved
  method's own slots, so `runMeasured_no_slots`: a method with none makes no calls. Together (`run_calls`): KERNEL's
  `notCallable` and `tooManyCalls` are unreachable from `Lang.program`.
* `bodyOf_callData`: every callable Body (a grant with at most `rightsMax` rights) has call data,
  and that data reads back as exactly that Body; `callData_bodyOf`: every Body read back has call
  data reading back to it. `callData_not_callable`: a kind an object may not exercise has none.
  `callData_conforms`: call data of a Body within the language's bounds (`callFits`) is a value
  of `callTy`, so a method can return it. The converse (liveness: conforming data is refused only
  for a field whose bytes are not a digest) and extraction conformance are `Lang.Proofs.CallLive`.
-/
import Lang.Program
import Lang.Proofs.Load
import Lang.Proofs.Data

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type}

/-! ## Read: every Body read is callable -/

section
variable {digestOf : ByteArray → Option D}

theorem bodyOf_callable {d : Data} {b : Body D} (h : bodyOf digestOf d = .ok b) : b.callable = true := by
  unfold bodyOf at h
  split at h
  all_goals try simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' split at h)
  all_goals first | (simp at h; done) | (cases h; rfl)

theorem callsOf_go_callable : ∀ {fs : List (Label × Data)} {bs : List (Body D)},
    callsOf.go digestOf fs = .ok bs → ∀ b ∈ bs, b.callable = true
  | [], bs, h => by
    unfold callsOf.go at h; cases h; simp
  | (ℓ, o) :: fs, bs, h => by
    unfold callsOf.go at h
    split at h
    · exact callsOf_go_callable h
    · split at h
      · rename_i b hb
        cases hg : callsOf.go digestOf fs with
        | error e => rw [hg] at h; cases h
        | ok bs' =>
          rw [hg] at h; cases h
          intro x hx
          cases hx with
          | head => exact bodyOf_callable hb
          | tail _ hx => exact callsOf_go_callable hg x hx
      · cases h
    · cases h

theorem callsOf_callable {d : Data} {bs : List (Body D)} (h : callsOf digestOf d = .ok bs) :
    ∀ b ∈ bs, b.callable = true := by
  unfold callsOf at h
  split at h
  · exact callsOf_go_callable h
  · cases h

theorem callsOf_go_length : ∀ {fs : List (Label × Data)} {bs : List (Body D)},
    callsOf.go digestOf fs = .ok bs → bs.length ≤ fs.length
  | [], bs, h => by
    unfold callsOf.go at h; cases h; simp
  | (ℓ, o) :: fs, bs, h => by
    unfold callsOf.go at h
    split at h
    · have := callsOf_go_length h; simp; omega
    · split at h
      · cases hg : callsOf.go digestOf fs with
        | error e => rw [hg] at h; cases h
        | ok bs' =>
          rw [hg] at h; cases h
          have := callsOf_go_length hg; simp; omega
      · cases h
    · cases h

/-- No more calls than the row has slots. -/
theorem callsOf_length {fs : List (Label × Data)} {bs : List (Body D)}
    (h : callsOf digestOf (.record fs) = .ok bs) : bs.length ≤ fs.length := by
  unfold callsOf at h
  exact callsOf_go_length h

end

/-! ## Write: every callable Body has call data, which reads back to it -/

theorem fillSlots_length {α : Type} {f : α → Data} :
    ∀ {ls : List Label} {xs : List α} {rs : List (Label × Data)},
      fillSlots f ls xs = some rs → rs.length = ls.length
  | [], [], rs, h => by simp [fillSlots] at h; subst h; rfl
  | [], _ :: _, rs, h => by simp [fillSlots] at h
  | l :: ls, [], rs, h => by
    simp only [fillSlots, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    simp [fillSlots_length h']
  | l :: ls, x :: xs, rs, h => by
    simp only [fillSlots, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    simp [fillSlots_length h']

theorem fillSlots_isSome {α : Type} {f : α → Data} :
    ∀ {ls : List Label} {xs : List α}, xs.length ≤ ls.length → (fillSlots f ls xs).isSome = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | l :: ls, [], _ => by
    simp only [fillSlots, Option.isSome_map]
    exact fillSlots_isSome (by simp)
  | l :: ls, x :: xs, h => by
    simp only [fillSlots, Option.isSome_map]
    exact fillSlots_isSome (by simp at h; omega)

theorem rightOf_rightData (r : Right) : rightOf (rightData r) = .ok r := by
  cases r <;> rfl

theorem rightsOf_fillSlots : ∀ {ls : List Label} {xs : List Right} {rs : List (Label × Data)},
    fillSlots rightData ls xs = some rs → rightsOf rs = .ok xs
  | [], [], rs, h => by simp [fillSlots] at h; subst h; rfl
  | [], _ :: _, rs, h => by simp [fillSlots] at h
  | l :: ls, [], rs, h => by
    simp only [fillSlots, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    simp [rightsOf, optData, optOf, rightsOf_fillSlots h', bind, Except.bind, pure, Except.pure]
  | l :: ls, x :: xs, rs, h => by
    simp only [fillSlots, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    simp [rightsOf, optData, optOf, rightOf_rightData, rightsOf_fillSlots h', bind, Except.bind, pure,
      Except.pure, Except.map]

theorem rightsOf_length : ∀ {rs : List (Label × Data)} {xs : List Right},
    rightsOf rs = .ok xs → xs.length ≤ rs.length
  | [], xs, h => by simp [rightsOf] at h; cases h; simp
  | (_, o) :: rs, xs, h => by
    simp only [rightsOf, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i r _
      split at h
      · cases h
      · rename_i xs' hxs
        cases h
        have := rightsOf_length hxs
        cases r <;> simp <;> omega

section
variable {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

/-- **Every callable Body is expressible**: its call data reads back as exactly it, given that a
digest's bytes decode to the digest. -/
theorem bodyOf_callData (hdig : ∀ x, digestOf (bytesOf x) = some x) {b : Body D} {d : Data}
    (h : callData bytesOf b = some d) : bodyOf digestOf d = .ok b := by
  cases b with
  | account asset owner =>
    simp only [callData, Option.some.injEq] at h; subst h
    simp [bodyOf, digestAt, digestData, hdig, bind, Except.bind, pure, Except.pure]
  | credit well acct amount via =>
    simp only [callData, Option.some.injEq] at h; subst h
    cases acct <;> cases via <;>
      simp [bodyOf, digestAt, digestData, acctRefData, acctRefOf, optData, optOf, natOf, hdig,
        bind, Except.bind, pure, Except.pure, Except.map]
  | grant target grantee rights parent =>
    simp only [callData, Option.map_eq_some_iff] at h
    obtain ⟨rs, hrs, rfl⟩ := h
    have hlen : rs.length ≤ rightsMax := by
      rw [fillSlots_length hrs]; simp [rightLabels, slotLabels]
    cases parent <;>
      simp [bodyOf, digestAt, digestData, optData, optOf, hdig, hlen, rightsOf_fillSlots hrs,
        bind, Except.bind, pure, Except.pure, Except.map]
  | invoke obj method args budget via =>
    simp only [callData, Option.some.injEq] at h; subst h
    cases via <;>
      simp [bodyOf, digestAt, digestData, optData, optOf, natOf, bytesAt, hdig,
        bind, Except.bind, pure, Except.pure, Except.map]
  | transfer src dst amount via once =>
    simp only [callData, Option.some.injEq] at h; subst h
    cases src <;> cases dst <;> cases via <;> cases once <;>
      simp [bodyOf, digestAt, digestData, acctRefData, acctRefOf, optData, optOf, natOf, bytesAt,
        hdig, bind, Except.bind, pure, Except.pure, Except.map]
  | enroll | rotate | install | create | write | law | revoke | issue => simp [callData] at h

/-- A kind an object may not exercise has no call data. -/
theorem callData_not_callable {b : Body D} (h : b.callable = false) : callData bytesOf b = none := by
  cases b <;> simp_all [Body.callable, callData]

/-- A callable Body has call data, unless it is a grant with more than `rightsMax` rights. -/
theorem callData_isSome {b : Body D} (h : b.callable = true)
    (hr : ∀ t g rs p, b = .grant t g rs p → rs.length ≤ rightsMax) : (callData bytesOf b).isSome = true := by
  cases b with
  | grant t g rs p =>
    simp only [callData, Option.isSome_map]
    exact fillSlots_isSome (by have := hr t g rs p rfl; simp [rightLabels, slotLabels]; omega)
  | _ => simp_all [Body.callable, callData]

/-- A grant read back carries at most `rightsMax` rights. -/
theorem bodyOf_rights {d : Data} {t g p : _} {rs : List Right}
    (h : bodyOf digestOf d = .ok (Body.grant t g rs p)) : rs.length ≤ rightsMax := by
  unfold bodyOf at h
  split at h
  all_goals try simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' split at h)
  all_goals first | (simp at h; done) | (cases h; exact Nat.le_trans (rightsOf_length ‹_›) ‹_›)

/-- **Every Body read back has call data reading back to it** (call data is not canonical: an
option row may leave any slot empty, so the data need not be the one read). -/
theorem callData_bodyOf (hdig : ∀ x, digestOf (bytesOf x) = some x) {d : Data} {b : Body D}
    (h : bodyOf digestOf d = .ok b) :
    ∃ d', callData bytesOf b = some d' ∧ bodyOf digestOf d' = .ok b := by
  have hs : (callData bytesOf b).isSome = true := by
    refine callData_isSome (bodyOf_callable h) ?_
    intro t g rs p hb
    subst hb
    exact bodyOf_rights h
  obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨d', hd', bodyOf_callData hdig hd'⟩

end

/-! ## Typed: in-bounds call data is a value of `callTy` -/

section
variable {bytesOf : D → ByteArray}

theorem conf_digest (hb : ∀ x, (bytesOf x).size ≤ Bounds.digestBytesMax) (x : D) :
    Conforms (digestData bytesOf x) .digest := .digest (hb x)

theorem conf_optDigest (hb : ∀ x, (bytesOf x).size ≤ Bounds.digestBytesMax) :
    ∀ v : Option D, Conforms (optData (digestData bytesOf) v) (optTy .digest)
  | none => .inj (A := .record []) rfl (.record .nil)
  | some x => .inj (A := .digest) rfl (conf_digest hb x)

theorem conf_acct (hb : ∀ x, (bytesOf x).size ≤ Bounds.digestBytesMax) :
    ∀ a : AcctRef D, Conforms (acctRefData bytesOf a) acctRefTy
  | .of o a => .inj (A := .record [("asset", .digest), ("owner", .digest)]) rfl
      (.record (.cons (conf_digest hb a) (.cons (conf_digest hb o) .nil)))
  | .well a => .inj (A := .digest) rfl (conf_digest hb a)

theorem conf_right : ∀ r : Right, rightFits r = true → Conforms (rightData r) rightTy
  | .enroll n, h => .inj (A := .nat) rfl (.nat (by simpa [rightFits] using h))
  | .invoke n, h => .inj (A := .nat) rfl (.nat (by simpa [rightFits] using h))
  | .transfer n, h => .inj (A := .nat) rfl (.nat (by simpa [rightFits] using h))
  | .credit n, h => .inj (A := .nat) rfl (.nat (by simpa [rightFits] using h))
  | .mutate, _ => .inj (A := .record []) rfl (.record .nil)
  | .observe, _ => .inj (A := .record []) rfl (.record .nil)

theorem conf_rights : ∀ {ls : List Label} {rs : List Right} {fs : List (Label × Data)},
    fillSlots rightData ls rs = some fs → (∀ r ∈ rs, rightFits r = true) →
      RowConforms fs (ls.map fun l => (l, optTy rightTy))
  | [], [], fs, h, _ => by simp [fillSlots] at h; subst h; exact .nil
  | [], _ :: _, fs, h, _ => by simp [fillSlots] at h
  | l :: ls, [], fs, h, hr => by
    simp only [fillSlots, Option.map_eq_some_iff] at h
    obtain ⟨fs', h', rfl⟩ := h
    exact .cons (.inj (A := .record []) rfl (.record .nil)) (conf_rights h' hr)
  | l :: ls, x :: xs, fs, h, hr => by
    simp only [fillSlots, Option.map_eq_some_iff] at h
    obtain ⟨fs', h', rfl⟩ := h
    exact .cons (.inj (A := rightTy) rfl (conf_right x (hr x (by simp))))
      (conf_rights h' (fun r hm => hr r (by simp [hm])))

/-- **In-bounds call data is a value of `callTy`**: so a method can return every callable Body
whose literals are values of the language (`callFits`), given the digest codec's bound. -/
theorem callData_conforms (hb : ∀ x, (bytesOf x).size ≤ Bounds.digestBytesMax) {b : Body D} {d : Data}
    (hf : callFits b = true) (h : callData bytesOf b = some d) : Conforms d callTy := by
  cases b with
  | account asset owner =>
    simp only [callData, Option.some.injEq] at h; subst h
    exact .inj rfl (.record (.cons (conf_digest hb asset) (.cons (conf_digest hb owner) .nil)))
  | credit well acct amount via =>
    simp only [callData, Option.some.injEq] at h; subst h
    simp only [callFits, decide_eq_true_eq] at hf
    exact .inj rfl (.record (.cons (conf_acct hb acct) (.cons (.nat hf) (.cons (conf_optDigest hb via)
      (.cons (conf_digest hb well) .nil)))))
  | grant target grantee rights parent =>
    simp only [callData, Option.map_eq_some_iff] at h
    obtain ⟨rs, hrs, rfl⟩ := h
    simp only [callFits, List.all_eq_true] at hf
    exact .inj rfl (.record (.cons (conf_digest hb grantee) (.cons (conf_optDigest hb parent)
      (.cons (.record (conf_rights hrs hf)) (.cons (conf_digest hb target) .nil)))))
  | invoke obj method args budget via =>
    simp only [callData, Option.some.injEq] at h; subst h
    simp only [callFits, Bool.and_eq_true, decide_eq_true_eq] at hf
    exact .inj rfl (.record (.cons (.bytes hf.2) (.cons (.nat hf.1.2) (.cons (.nat hf.1.1)
      (.cons (conf_digest hb obj) (.cons (conf_optDigest hb via) .nil))))))
  | transfer src dst amount via once =>
    simp only [callData, Option.some.injEq] at h; subst h
    simp only [callFits, Bool.and_eq_true, decide_eq_true_eq] at hf
    have ho : Conforms (optData Data.bytes once) (optTy .bytes) := by
      cases once with
      | none => exact .inj (A := .record []) rfl (.record .nil)
      | some k => exact .inj (A := .bytes) rfl (.bytes (by simpa using hf.2))
    exact .inj rfl (.record (.cons (.nat hf.1) (.cons (conf_acct hb dst) (.cons ho
      (.cons (conf_acct hb src) (.cons (conf_optDigest hb via) .nil))))))
  | enroll | rotate | install | create | write | law | revoke | issue => simp [callData] at h

end

/-! ## The deployed run: its calls are callable and at most `callsMax` -/

theorem extractRow_length {m : Machine} : ∀ {row : List (Label × Ty)} {fuel : Nat}
    {fs : List (Label × (Term × Env))} {ds : List (Label × Data)} {f : Nat},
    m.extractRow row fuel fs = .ok (ds, f) → ds.length = row.length := by
  intro row
  induction row with
  | nil =>
    intro fuel fs ds f h
    cases fs <;> simp [Machine.extractRow] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | cons x row ih =>
    intro fuel fs ds f h
    obtain ⟨ℓ, A⟩ := x
    cases fs with
    | nil => simp [Machine.extractRow] at h
    | cons y fs =>
      obtain ⟨ℓ', t, env⟩ := y
      simp only [Machine.extractRow] at h
      repeat' split at h
      all_goals first | (simp at h; done) | skip
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [ih ‹m.extractRow row _ fs = _›]

theorem extract_record {m : Machine} {row : List (Label × Ty)} {fuel : Nat} {v : Val} {d : Data} {f : Nat}
    (h : m.extract (.record row) fuel v = .ok (d, f)) : ∃ ds, d = .record ds ∧ ds.length = row.length := by
  simp only [Machine.extract] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨_, rfl, extractRow_length ‹_›⟩

theorem extractRow_head {m : Machine} {ℓ ℓ' : Label} {A : Ty} {row : List (Label × Ty)} {fuel : Nat}
    {fs : List (Label × (Term × Env))} {d : Data} {ds : List (Label × Data)} {f : Nat}
    (h : m.extractRow ((ℓ, A) :: row) fuel fs = .ok ((ℓ', d) :: ds, f)) :
    ∃ fuel' v f', m.extract A fuel' v = .ok (d, f') := by
  cases fs with
  | nil => simp [Machine.extractRow] at h
  | cons y fs =>
    obtain ⟨_, t, env⟩ := y
    simp only [Machine.extractRow] at h
    repeat' split at h
    all_goals first | (simp at h; done) | skip
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq] at h
    obtain ⟨⟨⟨_, hd⟩, _⟩, _⟩ := h
    subst hd
    exact ⟨_, _, _, ‹_›⟩

/-- The calls half of a method's extracted result is a row of exactly its declared slots. -/
theorem extract_result_calls {m : Machine} {S : Ty} {ks : List Ty} {E : Ty} {es : Nat} {fuel : Nat} {v : Val}
    {c e st : Data} {left : Nat}
    (h : m.extract (resultTy S ks E es) fuel v = .ok (.record [("calls", c), ("edits", e), ("state", st)], left)) :
    ∃ cs, c = .record cs ∧ cs.length = ks.length := by
  unfold resultTy at h
  simp only [Machine.extract] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq, Data.record.injEq] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨_, _, _, hc⟩ := extractRow_head ‹_›
  obtain ⟨cs, rfl, hl⟩ := extract_record hc
  exact ⟨cs, rfl, by simp [hl, slotLabels]⟩

/-- A method resolves with at most `callsMax` call slots (`methodSig` checks the row). -/
theorem resolveMethod_slots {p : Package} {method : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) p method = .ok x) : x.2.calls.length ≤ Kernel.Bounds.callsMax := by
  unfold resolveMethod at h
  simp only [pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq] at h
  subst h
  exact (methodSig_spec ‹_›).2.1

/-- The calls `runMeasured` returns are `callsOf` of the calls half of the result extracted at
the method's own result type: the package the run loaded, the method it resolved, its slots. -/
theorem runMeasuredWith_calls {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {loader : Pinned D → Nat → ByteArray → Loaded → Except (Refusal D) (Loaded × Nat)}
    {charge : Loaded → Nat}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf (runSetupWith bytesOf digestOf loader charge) look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ (L : Loaded) (g : Nat) (p : Package) (x : Label × Sig) (m : Machine) (fuel : Nat)
      (v : Val) (c e st : Data) (left : Nat),
      loader look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧
      L.pkgs[g]? = some p ∧ resolveMethod (D := D) p method = .ok x ∧
      m.extract (resultTy p.state x.2.calls (editTy p.rels) x.2.edits) fuel v =
        .ok (.record [("calls", c), ("edits", e), ("state", st)], left) ∧
      callsOf digestOf c = .ok calls := by
  unfold runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hp, hres, -, -, -, -, rfl⟩ := runSetupWith_spec hS
  simp only at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -, -, -⟩ := h
  exact ⟨L, g, p, (ℓ, sg), _, _, _, _, _, _, _, hl, hp, hres, by assumption, by assumption⟩

/-- **A method makes at most its declared calls**: the calls of a run are no more than the call
slots of the method resolved in the package the run loaded. -/
theorem runMeasuredWith_calls_slots {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {loader : Pinned D → Nat → ByteArray → Loaded → Except (Refusal D) (Loaded × Nat)}
    {charge : Loaded → Nat}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf (runSetupWith bytesOf digestOf loader charge) look rv pkg state method args r budget = .ok (s, calls, rows, t, n))
    {L : Loaded} {g : Nat} {p : Package} {x : Label × Sig}
    (hl : loader look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hx : resolveMethod (D := D) p method = .ok x) :
    calls.length ≤ x.2.calls.length ∧ ∀ b ∈ calls, b.callable = true := by
  obtain ⟨L', g', p', x', _, _, _, c, _, _, _, hl', hp', hx', he, hc⟩ := runMeasuredWith_calls h
  rw [hl] at hl'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hl'
  obtain ⟨rfl, rfl⟩ := hl'
  rw [hp] at hp'
  cases hp'
  rw [hx] at hx'
  cases hx'
  obtain ⟨cs, rfl, hcs⟩ := extract_result_calls he
  exact ⟨hcs ▸ callsOf_length hc, callsOf_callable hc⟩

theorem runMeasured_calls {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ (L : Loaded) (g : Nat) (p : Package) (x : Label × Sig) (m : Machine) (fuel : Nat)
      (v : Val) (c e st : Data) (left : Nat),
      load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧
      L.pkgs[g]? = some p ∧ resolveMethod (D := D) p method = .ok x ∧
      m.extract (resultTy p.state x.2.calls (editTy p.rels) x.2.edits) fuel v =
        .ok (.record [("calls", c), ("edits", e), ("state", st)], left) ∧
      callsOf digestOf c = .ok calls := by
  exact runMeasuredWith_calls (loader := load digestOf) (charge := fun _ => 0) h

/-- **A method makes at most its declared calls**: the calls of a run are no more than the call
slots of the method resolved in the package the run loaded. -/
theorem runMeasured_calls_slots {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n))
    {L : Loaded} {g : Nat} {p : Package} {x : Label × Sig}
    (hl : load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hx : resolveMethod (D := D) p method = .ok x) :
    calls.length ≤ x.2.calls.length ∧ ∀ b ∈ calls, b.callable = true := by
  exact runMeasuredWith_calls_slots (loader := load digestOf) (charge := fun _ => 0) h hl hp hx

/-- A method with no call slots makes no calls (Hosting's `method_no_calls` is such a type). -/
theorem runMeasured_no_slots {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n))
    {L : Loaded} {g : Nat} {p : Package} {ℓ : Label} {A : Ty} {rs : List (Label × RelRead)} {es : Nat}
    (hl : load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hx : resolveMethod (D := D) p method = .ok (ℓ, ⟨A, [], rs, es⟩)) :
    calls = [] :=
  List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (runMeasured_calls_slots h hl hp hx).1)

/-- Extraction facts independent of how the invocation's library was prepared.
The setup may depend on this invocation's authenticated row view and self. -/
theorem runMeasuredWith_extract {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {setup : Pinned D → RowView D → D → Slots → Nat → ByteArray → Req D → Except (Refusal D) RunSetup}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf setup look rv pkg state method args r budget =
      .ok (s, calls, rows, t, n)) :
    ∃ (S : RunSetup) (fuel : Nat) (v : Val) (c e st : Data) (left : Nat),
      setup look rv pkg state method args r = .ok S ∧
      (Machine.mk S.lib).extract S.ty fuel v =
        .ok (.record [("calls", c), ("edits", e), ("state", st)], left) ∧
      callsOf digestOf c = .ok calls := by
  unfold runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -, -, -⟩ := h
  exact ⟨_, _, _, _, _, _, _, by assumption, by assumption, by assumption⟩

/-- **The calls `Lang.program` hands KERNEL**: at most `callsMax` of them, each of a kind an object
may exercise. So KERNEL's `tooManyCalls` and `notCallable` assertions never fire on a Lang method:
they stay as KERNEL's own checks where calls enter, since `Program` is abstract to it (law 4). -/
theorem run_calls {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t : Nat}
    (h : (program bytesOf digestOf).run look rv pkg state method args r budget = .ok (s, calls, rows, t)) :
    calls.length ≤ Kernel.Bounds.callsMax ∧ ∀ b ∈ calls, b.callable = true := by
  change (runMeasuredLive bytesOf digestOf look rv pkg state method args r budget).map
    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1)) = .ok (s, calls, rows, t) at h
  simp only [Except.map] at h
  split at h
  · cases h
  · rename_i x hx
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -, -⟩ := h
    obtain ⟨S, fuel, v, c, e, st, left, hS, he, hc⟩ :=
      runMeasuredWith_extract (bytesOf := bytesOf) (digestOf := digestOf)
        (setup := runSetupLive bytesOf digestOf) hx
    obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hp, hres, -, -, -, -, hSdef⟩ :=
      runSetupWith_spec (loader := loadLive digestOf rv r.self)
        (charge := Loaded.preparationCost) hS
    subst S
    obtain ⟨cs, rfl, hcs⟩ := extract_result_calls he
    exact ⟨Nat.le_trans (hcs ▸ callsOf_length hc) (resolveMethod_slots hres), callsOf_callable hc⟩

end Nanodregg.Lang
