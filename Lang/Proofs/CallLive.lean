/-
# Lang.Proofs.CallLive — call data that conforms to its type is refused only for a non-digest field

`Lang.Proofs.Call` proves the forward half: a callable Body in bounds has call data of `callTy`
(`callData_conforms`). This is the converse, liveness. `bodyOf_live`: data conforming to `callTy`
reads as a Body, or the refusal is `PATH: not a digest` for bytes the digest decoder refuses, held
at exactly that label path of the data (`Live`, `DigestAt`, `Names`), the one thing a type cannot say. `callsOf_live`: the same for a calls
row conforming to `callsTy ks` over call slots, with the slot named (`DigestRefusal`).
`extract_conforms`: a value typed at a type extracts to data conforming to it (forcing each
suspension is a typed run, `force_typed`, `unknot_typed`). `callsOf_go_kinds`: the calls a
conforming row reads match, in order and one to one, a sublist of its slots, each call of its own
slot's kinds (`Matched`, `KindOf`). `runMeasured_kinds` / `runMeasured_calls_le`: the same at the
deployed run (typed by `invoke_never_stuck`, carried to data by `extract_conforms`), so a method
makes at most as many calls as it declares slots and never two from one slot.
`bodyOf_ok_of_total` is the identity-digest corollary.
-/
import Lang.Proofs.Call
import Lang.Proofs.Invoke

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} {digestOf : ByteArray → Option D} {rc : ReceiptCheck} {d0 : Data}

/-- Digest leaf `b` sits in data `d` at label path `p` (a `bytes` leaf never does: since LANG-38
only a field typed `digest` can be refused as not a digest). Each record field on the way is named in
the path (`field`). A sum arm is either named (`arm`, as an account's `well` is) or passed over (`inj`,
as an option's `some`, a call's kind, an account's `of`). -/
inductive DigestAt (b : ByteArray) : List Label → Data → Prop
  | here : DigestAt b [] (.digest b)
  | inj {p : List Label} {ℓ : Label} {d : Data} : DigestAt b p d → DigestAt b p (.inj ℓ d)
  | arm {p : List Label} {ℓ : Label} {d : Data} : DigestAt b p d → DigestAt b (ℓ :: p) (.inj ℓ d)
  | field {p : List Label} {fs : List (Label × Data)} {ℓ : Label} {d : Data} :
      (ℓ, d) ∈ fs → DigestAt b p d → DigestAt b (ℓ :: p) (.record fs)

/-- `f` is how a refusal names label path `p`: its labels joined by `.` (`acct.owner`). -/
inductive Names : List Label → String → Prop
  | one (ℓ : Label) : Names [ℓ] ℓ
  | cons (ℓ : Label) {p : List Label} {f : String} : Names p f → Names (ℓ :: p) (ℓ ++ "." ++ f)

/-- Data `d` sits in `d0` at path `p`: every digest leaf of `d` is a leaf of `d0`, `p` deeper. -/
def Under (p : List Label) (d d0 : Data) : Prop := ∀ q b, DigestAt b q d → DigestAt b (p ++ q) d0

/-- Reading `d0` gives `x`, which fails, if at all, only because bytes of `d0` are refused by
`digestOf`, and the refusal names the path in `d0` whose digest leaf holds them. -/
def Live (digestOf : ByteArray → Option D) (d0 : Data) {α : Type} (x : Except String α) : Prop :=
  ∀ e, x = .error e → ∃ (p : List Label) (f : String) (b : ByteArray),
    digestOf b = none ∧ DigestAt b p d0 ∧ Names p f ∧ e = s!"{f}: not a digest"

theorem Live.lift {d0 d1 : Data} {α : Type} {x : Except String α} (hx : Live digestOf d0 x)
    (hs : ∀ p b, DigestAt b p d0 → DigestAt b p d1) : Live digestOf d1 x := by
  intro e h
  obtain ⟨p, f, b, hn, hb, hf, rfl⟩ := hx e h
  exact ⟨p, f, b, hn, hs p b hb, hf, rfl⟩

theorem under_field {ℓ : Label} {d : Data} {fs : List (Label × Data)} {k : Label} (hm : (ℓ, d) ∈ fs) :
    Under [ℓ] d (.inj k (.record fs)) := fun _ _ hb => .inj (.field hm hb)

theorem Under.some {p : List Label} {d d0 : Data} (h : Under p (.inj "some" d) d0) : Under p d d0 :=
  fun q b hb => h q b (.inj hb)

theorem Under.of {p : List Label} {ℓ : Label} {d d0 : Data} (h : Under p (.inj ℓ d) d0) :
    Under (p ++ [ℓ]) d d0 := fun q b hb => by simpa using h (ℓ :: q) b (.arm hb)

theorem Under.under {p : List Label} {ℓ ℓ' : Label} {fs : List (Label × Data)} {d d0 : Data}
    (h : Under p (.inj ℓ (.record fs)) d0) (hm : (ℓ', d) ∈ fs) : Under (p ++ [ℓ']) d d0 :=
  fun q b hb => by simpa using h (ℓ' :: q) b (.inj (.field hm hb))

theorem Live.pure {α : Type} (a : α) : Live digestOf d0 (Except.ok a : Except String α) := by
  intro e h; cases h

theorem Live.bind {α β : Type} {x : Except String α} {k : α → Except String β} (hx : Live digestOf d0 x)
    (hk : ∀ a, Live digestOf d0 (k a)) : Live digestOf d0 (x >>= k) := by
  intro e h
  cases hx' : x with
  | error e' =>
    rw [hx'] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; exact hk a e h

theorem Live.map {α β : Type} {x : Except String α} (g : α → β) (hx : Live digestOf d0 x) : Live digestOf d0 (g <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; simp only [Functor.map, Except.map] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; simp [Functor.map, Except.map] at h

theorem Live.map' {α β : Type} {x : Except String α} (g : α → β) (hx : Live digestOf d0 x) : Live digestOf d0 (x.map g) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; simp only [Except.map] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; simp [Except.map] at h

theorem conf_bytes {d : Data} (h : Conforms d .bytes) : ∃ b, d = .bytes b := by cases h; exact ⟨_, rfl⟩

theorem conf_digestD {d : Data} (h : Conforms d .digest) : ∃ b, d = .digest b := by cases h; exact ⟨_, rfl⟩

theorem conf_nat {d : Data} (h : Conforms d .nat) : ∃ n, d = .nat n := by cases h; exact ⟨_, rfl⟩

theorem conf_unit {d : Data} (h : Conforms d (.record [])) : d = .record [] := by
  cases h with | record hr => cases hr; rfl

theorem conf_opt {d : Data} {T : Ty} (h : Conforms d (optTy T)) :
    d = .inj "none" (.record []) ∨ ∃ d', d = .inj "some" d' ∧ Conforms d' T := by
  cases h with
  | inj hf hd =>
    simp only [Row.find?] at hf
    split at hf
    · cases hf; subst_vars; exact .inl (by rw [conf_unit hd])
    · split at hf
      · cases hf; subst_vars; exact .inr ⟨_, rfl, hd⟩
      · cases hf

/-- A digest field named `f`, the name of its path `p` in `d0`, refuses only bytes at `p`. -/
theorem digest_live {d d0 : Data} {p : List Label} (f : String) (hf : Names p f) (h : Conforms d .digest)
    (hu : Under p d d0) : Live digestOf d0 (digestAt digestOf f d) := by
  obtain ⟨b, rfl⟩ := conf_digestD h
  intro e he
  simp only [digestAt] at he
  split at he
  · cases he
  · rename_i hn; cases he; exact ⟨p, f, b, hn, by simpa using hu [] b .here, hf, rfl⟩

theorem optDigest_live {d d0 : Data} {p : List Label} (f g : String) (hf : Names p f) (h : Conforms d (optTy .digest))
    (hu : Under p d d0) : Live digestOf d0 (optOf (digestAt digestOf f) g d) := by
  rcases conf_opt h with rfl | ⟨d', rfl, hd⟩
  · simp only [optOf]; exact Live.pure _
  · simp only [optOf]; exact Live.map' _ (digest_live f hf hd hu.some)

theorem optBytes_live {d : Data} (f g : String) (h : Conforms d (optTy .bytes)) :
    Live digestOf d0 (optOf (bytesAt f) g d) := by
  rcases conf_opt h with rfl | ⟨d', rfl, hd⟩
  · simp only [optOf]; exact Live.pure _
  · obtain ⟨b, rfl⟩ := conf_bytes hd; simp only [optOf, bytesAt]; exact Live.map' _ (Live.pure _)

theorem natOf_live {d : Data} (f : String) (h : Conforms d .nat) : Live digestOf d0 (natOf f d) := by
  obtain ⟨n, rfl⟩ := conf_nat h; exact Live.pure _

theorem bytesAt_live {d : Data} (f : String) (h : Conforms d .bytes) : Live digestOf d0 (bytesAt f d) := by
  obtain ⟨b, rfl⟩ := conf_bytes h; exact Live.pure _

theorem names_dot {f g s : String} (hs : s = f ++ "." ++ g) : Names ([f] ++ [g]) s :=
  hs ▸ .cons f (.one g)

/-- An account named `f` (at path `[f]` in `d0`) refuses only bytes at `f.owner`, `f.asset` or
`f.well`, named so. -/
theorem acctRef_live {d d0 : Data} (f : String) (h : Conforms d acctRefTy) (hu : Under [f] d d0) :
    Live digestOf d0 (acctRefOf digestOf f d) := by
  cases h with
  | inj hf hd =>
    simp only [Row.find?] at hf
    split at hf
    · cases hf; subst_vars
      cases hd with
      | record hr =>
        cases hr with
        | cons ha hr =>
          cases hr with
          | cons ho hr =>
            cases hr
            simp only [acctRefOf]
            exact Live.bind (digest_live _ (names_dot (g := "owner") (by simp only [toString, String.append_assoc]; rfl)) ho (hu.under (by simp))) fun _ =>
              Live.bind (digest_live _ (names_dot (g := "asset") (by simp only [toString, String.append_assoc]; rfl)) ha (hu.under (by simp))) fun _ => Live.pure _
    · split at hf
      · cases hf; subst_vars
        simp only [acctRefOf]; exact Live.map' _ (digest_live _ (names_dot (g := "well") (by simp only [toString, String.append_assoc]; rfl)) hd hu.of)
      · cases hf

theorem right_ok {d : Data} (h : Conforms d rightTy) : ∃ r, rightOf d = .ok r := by
  cases h with
  | inj hf hd =>
    simp only [Row.find?] at hf
    repeat' split at hf
    all_goals first | cases hf | skip
    all_goals subst_vars
    · obtain ⟨n, rfl⟩ := conf_nat hd; exact ⟨_, rfl⟩
    · obtain ⟨n, rfl⟩ := conf_nat hd; exact ⟨_, rfl⟩
    · obtain ⟨n, rfl⟩ := conf_nat hd; exact ⟨_, rfl⟩
    · rw [conf_unit hd]; exact ⟨_, rfl⟩
    · rw [conf_unit hd]; exact ⟨_, rfl⟩
    · obtain ⟨n, rfl⟩ := conf_nat hd; exact ⟨_, rfl⟩

theorem rights_live : ∀ {rs : List (Label × Data)} {ls : List Label},
    RowConforms rs (ls.map fun l => (l, optTy rightTy)) → Live digestOf d0 (rightsOf rs)
  | [], _, _ => Live.pure _
  | (_, o) :: rs, [], h => by cases h
  | (_, o) :: rs, l :: ls, h => by
    cases h with
    | cons ho hr =>
      simp only [rightsOf]
      refine Live.bind ?_ fun _ => Live.bind (rights_live hr) fun _ => Live.pure _
      rcases conf_opt ho with rfl | ⟨d', rfl, hd⟩
      · simp only [optOf]; exact Live.pure _
      · obtain ⟨r, hr⟩ := right_ok hd; simp only [optOf, hr]; exact Live.map' _ (Live.pure _)

theorem rowConforms_length : ∀ {ds : List (Label × Data)} {r : List (Label × Ty)}, RowConforms ds r →
    ds.length = r.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [rowConforms_length h]

/-- The `invoke` arm's `args`, a value of the slot's argument type, has bytes (`encodeData_of_conforms`,
LANG-77): the encoder is live at any data. -/
theorem argsBytes_live {A : Ty} {a : Data} (hA : Wire.dataTy A = true) (h : Conforms a A) :
    Live digestOf d0 (argsBytes (some A) "args" a) := by
  obtain ⟨b, hb⟩ := encodeData_of_conforms hA h
  simp only [argsBytes, hb]
  exact Live.pure _

/-- The four arms every slot may hold, read at any invoke argument type (they do not read it). -/
private theorem bodyOf_live_fixed {A : Option Ty} {ℓ : Label} {T : Ty} {d' : Data}
    (hf : Row.find? ℓ (callArms none) = some T) (hd : Conforms d' T) :
    Live digestOf (.inj ℓ d') (bodyOf digestOf A (.inj ℓ d')) := by
  simp only [callArms, accountArm, creditArm, grantArm, transferArm, Row.find?] at hf
  split at hf
  · cases hf; subst_vars
    cases hd with | record hr => cases hr with | cons h1 hr => cases hr with | cons h2 hr =>
    cases hr
    simp only [bodyOf]
    exact Live.bind (digest_live _ (.one _) h1 (under_field (by simp))) fun _ => Live.bind (digest_live _ (.one _) h2 (under_field (by simp))) fun _ => Live.pure _
  split at hf
  · cases hf; subst_vars
    cases hd with | record hr => cases hr with | cons h1 hr => cases hr with | cons h2 hr =>
    cases hr with | cons h3 hr => cases hr with | cons h4 hr =>
    cases hr
    simp only [bodyOf]
    exact Live.bind (digest_live _ (.one _) h4 (under_field (by simp))) fun _ => Live.bind (acctRef_live _ h1 (under_field (by simp))) fun _ =>
      Live.bind (natOf_live _ h2) fun _ => Live.bind (optDigest_live _ _ (.one _) h3 (under_field (by simp))) fun _ => Live.pure _
  split at hf
  · cases hf; subst_vars
    cases hd with | record hr => cases hr with | cons h1 hr => cases hr with | cons h2 hr =>
    cases hr with | cons h3 hr => cases hr with | cons h4 hr =>
    cases hr
    cases h3 with
    | record hrs =>
      have hlen := rowConforms_length hrs
      simp only [List.length_map, rightLabels, slotLabels, List.length_range] at hlen
      simp only [bodyOf, hlen, rightsMax, Nat.le_refl, if_true]
      exact Live.bind (digest_live _ (.one _) h4 (under_field (by simp))) fun _ => Live.bind (digest_live _ (.one _) h1 (under_field (by simp))) fun _ =>
        Live.bind (rights_live hrs) fun _ => Live.bind (optDigest_live _ _ (.one _) h2 (under_field (by simp))) fun _ => Live.pure _
  split at hf
  · cases hf; subst_vars
    cases hd with | record hr => cases hr with | cons h1 hr => cases hr with | cons h2 hr =>
    cases hr with | cons h3 hr => cases hr with | cons h4 hr => cases hr with | cons h5 hr =>
    cases hr
    simp only [bodyOf]
    exact Live.bind (acctRef_live _ h4 (under_field (by simp))) fun _ => Live.bind (acctRef_live _ h2 (under_field (by simp))) fun _ =>
      Live.bind (natOf_live _ h1) fun _ => Live.bind (optDigest_live _ _ (.one _) h5 (under_field (by simp))) fun _ =>
      Live.bind (optBytes_live _ _ h3) fun _ => Live.pure _
  cases hf

/-- The arm a value of `callTy (some A')` sits at: one of the four every slot has, or the `invoke`
arm at `A'`. -/
private theorem find_some {ℓ : Label} {A' T : Ty} (hf : Row.find? ℓ (callArms (some A')) = some T) :
    Row.find? ℓ (callArms none) = some T ∨ (ℓ = "invoke" ∧ T = invokeArm A') := by
  simp only [callArms, Row.find?] at hf ⊢
  split at hf
  · cases hf; subst_vars; left; rfl
  split at hf
  · cases hf; subst_vars; left; rfl
  split at hf
  · cases hf; subst_vars; left; rfl
  split at hf
  · cases hf; subst_vars; right; exact ⟨rfl, rfl⟩
  split at hf
  · cases hf; subst_vars; left; rfl
  cases hf

/-- **Liveness**: data conforming to `callTy A` (the slot's invoke arm at `A`, a type the wire
carries) reads as a Body, unless some field's bytes are not a digest (`bodyOf`'s only refusal the
type does not rule out: the encoder never refuses a value of `A`, `argsBytes_live`). -/
theorem bodyOf_live {A : Option Ty} (hA : ∀ A', A = some A' → Wire.dataTy A' = true) {d : Data}
    (h : Conforms d (callTy A)) : Live digestOf d (bodyOf digestOf A d) := by
  cases h with
  | inj hf hd =>
    cases A with
    | none => exact bodyOf_live_fixed hf hd
    | some A' =>
      rcases find_some hf with hf' | ⟨rfl, rfl⟩
      · exact bodyOf_live_fixed hf' hd
      · simp only [invokeArm] at hd
        cases hd with | record hr => cases hr with | cons h1 hr => cases hr with | cons h2 hr =>
        cases hr with | cons h3 hr => cases hr with | cons h4 hr => cases hr with | cons h5 hr =>
        cases hr
        simp only [bodyOf]
        exact Live.bind (digest_live _ (.one _) h4 (under_field (by simp))) fun _ => Live.bind (natOf_live _ h3) fun _ =>
          Live.bind (argsBytes_live (hA A' rfl) h1) fun _ => Live.bind (natOf_live _ h2) fun _ =>
          Live.bind (optDigest_live _ _ (.one _) h5 (under_field (by simp))) fun _ => Live.pure _

/-- The identity-digest corollary (no real digest codec is total; `bodyOf_live` is the statement):
under a decoder that accepts every byte string, conforming call data always reads. -/
theorem bodyOf_ok_of_total (htot : ∀ b, (digestOf b).isSome = true) {A : Option Ty}
    (hA : ∀ A', A = some A' → Wire.dataTy A' = true) {d : Data} (h : Conforms d (callTy A)) :
    ∃ b : Body D, bodyOf digestOf A d = .ok b := by
  cases hb : bodyOf digestOf A d with
  | ok b => exact ⟨b, rfl⟩
  | error e =>
    obtain ⟨_, _, b, hn, -, -, -⟩ := bodyOf_live hA h e hb
    have := htot b
    rw [hn] at this; cases this

/-! ## Extraction: a typed value extracts to data of its type -/

section
variable {Δ : List Ty}

theorem force_typed {m : Machine} (hlib : LibTy Δ m.lib) {fuel : Nat} {t : Term} {env : Env} {Γ : List Ty} {A : Ty}
    {v : Val} {f : Nat} (he : EnvTy Δ env Γ) (ht : HasType Δ Γ t A) (h : m.force fuel t env = .ok (v, f)) :
    ValTy Δ v A := by
  unfold Machine.force at h
  have hr := run_sound (cap := Bounds.stackMax) hlib fuel 0 (State.init t env) (.eval he ht .nil)
  split at h
  · rename_i v' used hv
    rw [hv] at hr
    cases h
    exact hr
  · cases h

theorem unknot_typed {m : Machine} (hlib : LibTy Δ m.lib) : ∀ {rounds fuel : Nat} {v : Val} {r : List (Label × Ty)}
    {fs : List (Label × (Term × Env))} {f : Nat}, ValTy Δ v (.record r) → m.unknot rounds fuel v = .ok (fs, f) →
    ThunksTy Δ fs r
  | rounds, fuel, .record fs', r, fs, f, hv, h => by
    cases hv with
    | record ht => simp only [Machine.unknot] at h; cases h; exact ht
  | 0, fuel, .knot b env, r, fs, f, _, h => by simp [Machine.unknot] at h
  | k + 1, fuel, .knot b env, r, fs, f, hv, h => by
    cases hv with
    | knot he hb =>
      simp only [Machine.unknot] at h
      split at h
      · rename_i v' fuel' hf
        exact unknot_typed hlib (force_typed hlib (.cons (.knot he hb) he) hb hf) h
      · cases h
  | _, _, .nat _, _, _, _, hv, _ => by cases hv
  | _, _, .bool _, _, _, _, hv, _ => by cases hv
  | _, _, .bytes _, _, _, _, hv, _ => by cases hv
  | _, _, .digest _, _, _, _, hv, _ => by cases hv
  | _, _, .clo _ _, _, _, _, hv, _ => by cases hv
  | _, _, .inj _ _, _, _, _, hv, _ => by cases hv

mutual
theorem extract_conforms {m : Machine} (hlib : LibTy Δ m.lib) : ∀ (T : Ty) {fuel : Nat} {v : Val} {d : Data} {f : Nat},
    ValTy Δ v T → m.extract T fuel v = .ok (d, f) → Conforms d T
  | .nat, _, _, _, _, hv, h => by
    cases hv with | nat hn => simp only [Machine.extract] at h; cases h; exact .nat hn
  | .bool, _, _, _, _, hv, h => by
    cases hv with | bool => simp only [Machine.extract] at h; cases h; exact .bool
  | .bytes, _, _, _, _, hv, h => by
    cases hv with | bytes hn => simp only [Machine.extract] at h; cases h; exact .bytes hn
  | .digest, _, _, _, _, hv, h => by
    cases hv with | digest hn => simp only [Machine.extract] at h; cases h; exact .digest hn
  | .fn _ _, _, v, _, _, _, h => by cases v <;> simp [Machine.extract] at h
  | .record row, _, _, _, _, hv, h => by
    simp only [Machine.extract] at h
    split at h
    · rename_i fs fuel' hu
      split at h
      · rename_i ds fuel'' hr
        cases h
        exact .record (extractRow_conforms hlib row (unknot_typed hlib hv hu) hr)
      · cases h
    · cases h
  | .sum row, _, v, _, _, hv, h => by
    cases hv with
    | inj hf hw =>
      simp only [Machine.extract] at h
      split at h
      · rename_i d' fuel' ha
        cases h
        exact .inj hf (extractArm_conforms hlib row hf hw ha)
      · cases h

theorem extractArm_conforms {m : Machine} (hlib : LibTy Δ m.lib) : ∀ (row : List (Label × Ty)) {ℓ : Label} {A : Ty}
    {fuel : Nat} {w : Val} {d : Data} {f : Nat}, Row.find? ℓ row = some A → ValTy Δ w A →
    m.extractArm row ℓ fuel w = .ok (d, f) → Conforms d A
  | [], _, _, _, _, _, _, hf, _, _ => by cases hf
  | (k, B) :: row, ℓ, A, _, _, _, _, hf, hw, h => by
    simp only [Machine.extractArm] at h
    simp only [Row.find?] at hf
    split at h
    · rename_i hk
      rw [if_pos hk] at hf; cases hf
      exact extract_conforms hlib B hw h
    · rename_i hk
      rw [if_neg hk] at hf
      exact extractArm_conforms hlib row hf hw h

theorem extractRow_conforms {m : Machine} (hlib : LibTy Δ m.lib) : ∀ (row : List (Label × Ty)) {fuel : Nat}
    {fs : List (Label × (Term × Env))} {ds : List (Label × Data)} {f : Nat},
    ThunksTy Δ fs row → m.extractRow row fuel fs = .ok (ds, f) → RowConforms ds row
  | [], _, _, _, _, ht, h => by
    cases ht; simp only [Machine.extractRow] at h; cases h; exact .nil
  | (ℓ, A) :: row, _, _, _, _, ht, h => by
    cases ht with
    | cons he htm hrest =>
      simp only [Machine.extractRow, if_true] at h
      split at h
      · rename_i v fuel' hfo
        split at h
        · rename_i d fuel'' hx
          split at h
          · rename_i ds' f' hr
            cases h
            exact .cons (extract_conforms hlib A (force_typed hlib he htm hfo) hx)
              (extractRow_conforms hlib row hrest hr)
          · cases h
        · cases h
      · cases h
end
end

/-! ## Call slots: a slot's value is a call of one of the slot's arms -/

theorem find?_mem {α : Type} : ∀ {r : List (Label × α)} {ℓ : Label} {a : α}, Row.find? ℓ r = some a → (ℓ, a) ∈ r
  | [], _, _, h => by cases h
  | (k, b) :: r, ℓ, a, h => by
    simp only [Row.find?] at h
    split at h
    · rename_i hk; cases h; subst hk; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (find?_mem h)

/-- A value of a call slot's type is a value of `callTy` at the slot's invoke argument, injected
at one of the slot's arms. -/
theorem slot_conforms {T : Ty} {d : Data} (hT : callSlotOk T = true) (h : Conforms d T) :
    Conforms d (callTy (slotInvokeArg T)) ∧ ∃ arms ℓ d', T = .sum arms ∧ d = .inj ℓ d' ∧ ℓ ∈ arms.map Prod.fst := by
  cases T with
  | sum arms =>
    cases h with
    | inj hf hd =>
      simp only [callSlotOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hT
      obtain ⟨⟨-, -⟩, harms⟩ := hT
      have hm := find?_mem hf
      exact ⟨.inj (harms _ hm) hd, arms, _, _, rfl, rfl, List.mem_map.2 ⟨_, hm, rfl⟩⟩
  | _ => simp [callSlotOk] at hT

/-- A call slot's invoke argument type is one the wire carries (`callSlotOk` asks `invokeArgOk`,
LANG-77): what `bodyOf_live` needs of it. -/
theorem callSlotOk_dataTy {T : Ty} (hT : callSlotOk T = true) :
    ∀ A, slotInvokeArg T = some A → Wire.dataTy A = true := by
  intro A hA
  cases T with
  | sum arms =>
    simp only [callSlotOk, Bool.and_eq_true] at hT
    simp only [slotInvokeArg] at hA
    rw [hA] at hT
    have h2 : (some A).all invokeArgOk = true := hT.1.2
    simp only [Option.all, invokeArgOk, Bool.and_eq_true] at h2
    exact h2.2
  | _ => simp [callSlotOk] at hT

/-- The Body read from call data is of the kind its arm names. -/
theorem bodyOf_kind {A : Option Ty} {d : Data} {b : Body D} (h : bodyOf digestOf A d = .ok b) :
    ∃ d', d = .inj b.kindName d' := by
  unfold bodyOf at h
  split at h
  all_goals try simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' split at h)
  all_goals first | (simp at h; done) | (cases h; exact ⟨_, rfl⟩)

/-- Two lists matched one to one, in order, by `R`. -/
inductive Matched {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Matched R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Matched R as bs → Matched R (a :: as) (b :: bs)

theorem Matched.length_eq {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, Matched R as bs →
    as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length_eq]

theorem Matched.mem_left {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, Matched R as bs →
    ∀ a ∈ as, ∃ b ∈ bs, R a b
  | _, _, .nil, _, ha => by cases ha
  | _, _, .cons hr h, a, ha => by
    cases ha with
    | head => exact ⟨_, List.mem_cons_self .., hr⟩
    | tail _ ha => obtain ⟨b, hb, hab⟩ := h.mem_left a ha; exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem Matched.map_right {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {f : γ → β}
    (hRS : ∀ a c, R a (f c) → S a c) : ∀ {as : List α} {cs : List γ}, Matched R as (cs.map f) → Matched S as cs
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, h => by
    cases h with
    | cons hr h => exact .cons (hRS _ _ hr) (Matched.map_right hRS h)

/-- Call `b` is of a kind slot type `t` declares (`t = optTy (sum arms)`, `b`'s kind an arm). -/
def KindOf (b : Body D) (t : Ty) : Prop := ∃ arms, t = optTy (.sum arms) ∧ b.kindName ∈ arms.map Prod.fst

/-- The refusal `callsOf` gives reading calls data `c` when slot `ℓ` holds, at path `p` in its
call, bytes the digest decoder refuses: the slot and the path by name. -/
def DigestRefusal (digestOf : ByteArray → Option D) (c : Data) (e : Refusal D) : Prop :=
  ∃ (ℓ : Label) (p : List Label) (f : String) (b : ByteArray), digestOf b = none ∧ DigestAt b (ℓ :: p) c ∧
    Names p f ∧ e = .program s!"calls: {ℓ} {s!"{f}: not a digest"}"

theorem callsOf_go_live : ∀ {ks : List Ty} {ls : List Label} {fs : List (Label × Data)},
    ls.length = ks.length → RowConforms fs (ls.zip (ks.map optTy)) → (∀ k ∈ ks, callSlotOk k = true) →
    ∀ e, callsOf.go digestOf ks fs = .error e → DigestRefusal digestOf (.record fs) e
  | [], [], fs, _, hr, _, e, h => by
    simp only [List.map_nil, List.zip_nil_right] at hr
    cases hr; simp [callsOf.go] at h
  | k :: ks, ℓ :: ls, fs, hl, hr, hks, e, h => by
    simp only [List.map_cons, List.zip_cons_cons] at hr
    cases hr with
    | @cons _ d _ ds _ ho hr =>
      have hks' : ∀ k ∈ ks, callSlotOk k = true := fun k hk => hks k (List.mem_cons_of_mem _ hk)
      have hok := hks k (List.mem_cons_self ..)
      have tail : ∀ e, callsOf.go digestOf ks ds = .error e → DigestRefusal digestOf (.record ((ℓ, d) :: ds)) e := by
        intro e he
        obtain ⟨ℓ', p, f, b, hn, hb, hf, rfl⟩ := callsOf_go_live (by simpa using hl) hr hks' e he
        cases hb with
        | field hm hb' => exact ⟨ℓ', p, f, b, hn, .field (List.mem_cons_of_mem _ hm) hb', hf, rfl⟩
      rcases conf_opt ho with rfl | ⟨d', rfl, hd⟩
      · simp only [callsOf.go] at h; exact tail e h
      · simp only [callsOf.go] at h
        split at h
        · rename_i b hb
          cases hg : callsOf.go digestOf ks ds with
          | error e' => rw [hg] at h; cases h; exact tail _ hg
          | ok bs => rw [hg] at h; cases h
        · rename_i m hm
          cases h
          obtain ⟨p, f, b, hn, hb, hf, rfl⟩ :=
            bodyOf_live (callSlotOk_dataTy hok) (slot_conforms hok hd).1 m hm
          exact ⟨ℓ, p, f, b, hn, .field (List.mem_cons_self ..) (.inj hb), hf, rfl⟩
  | [], _ :: _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _, _, _ => by simp at hl

/-- **The calls a conforming row reads are its filled slots, in order, each of its own slot's
kinds**: a sublist of the row's slot types, matched one to one. So no slot yields two calls, and a
method makes at most as many calls as it has slots. -/
theorem callsOf_go_kinds : ∀ {ks : List Ty} {ls : List Label} {fs : List (Label × Data)} {bs : List (Body D)},
    ls.length = ks.length → RowConforms fs (ls.zip (ks.map optTy)) → (∀ k ∈ ks, callSlotOk k = true) →
    callsOf.go digestOf ks fs = .ok bs →
    ∃ ts, ts.Sublist ((ls.zip (ks.map optTy)).map Prod.snd) ∧ Matched KindOf bs ts
  | [], [], fs, bs, _, hr, _, h => by
    simp only [List.map_nil, List.zip_nil_right] at hr ⊢
    cases hr; simp [callsOf.go] at h; subst h; exact ⟨[], .slnil, .nil⟩
  | k :: ks, ℓ :: ls, fs, bs, hl, hr, hks, h => by
    simp only [List.map_cons, List.zip_cons_cons] at hr ⊢
    cases hr with
    | @cons _ d _ ds _ ho hr =>
      have hks' : ∀ k ∈ ks, callSlotOk k = true := fun k hk => hks k (List.mem_cons_of_mem _ hk)
      have hok := hks k (List.mem_cons_self ..)
      rcases conf_opt ho with rfl | ⟨d', rfl, hd⟩
      · simp only [callsOf.go] at h
        obtain ⟨ts, hts, hf⟩ := callsOf_go_kinds (by simpa using hl) hr hks' h
        exact ⟨ts, hts.cons _, hf⟩
      · simp only [callsOf.go] at h
        split at h
        · rename_i b hb
          cases hg : callsOf.go digestOf ks ds with
          | error e' => rw [hg] at h; cases h
          | ok bs' =>
            rw [hg] at h; cases h
            obtain ⟨ts, hts, hf⟩ := callsOf_go_kinds (by simpa using hl) hr hks' hg
            obtain ⟨-, arms, ℓ', d'', hT, hdd, hmem⟩ := slot_conforms hok hd
            obtain ⟨d3, hd3⟩ := bodyOf_kind hb
            rw [hdd] at hd3; cases hd3
            exact ⟨optTy k :: ts, hts.cons_cons _, .cons ⟨arms, by rw [hT], hmem⟩ hf⟩
        · cases h
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl

/-- **Liveness of a calls row**: data conforming to `callsTy ks` over call slot types is refused by
`callsOf` only for a slot field whose bytes are not a digest, named `calls: cI FIELD`. The encoder
of an invoke's `args` (LANG-77) never refuses: every slot's argument type is one the wire carries
(`callSlotOk`) and the datum conforms to it. -/
theorem callsOf_live {ks : List Ty} {c : Data} (hks : ∀ k ∈ ks, callSlotOk k = true) (h : Conforms c (callsTy ks))
    (e : Refusal D) (he : callsOf digestOf ks c = .error e) : DigestRefusal digestOf c e := by
  cases h with
  | record hr => exact callsOf_go_live (by simp [slotLabels]) hr hks e he

/-- `callSlotsOf` on a row of two slots of one call type, read off that type's `callSlotOk` (a slot
type that depends on a package parameter, as `Std.offer`'s does, is not decided: LANG-77). -/
theorem callSlotsOf_two (T U : Ty) :
    callSlotsOf [("c0", optTy T), ("c1", optTy U)] =
      if callSlotOk T then (if callSlotOk U then some [T, U] else none) else none := by
  have hl : slotLabels "c" 2 = ["c0", "c1"] := by decide
  simp only [callSlotsOf, callSlotOf, optTy, List.length_cons, List.length_nil, List.map, hl,
    Kernel.Bounds.callsMax, List.mapM, List.mapM.loop]
  split <;> cases h : callSlotOk T <;> cases h' : callSlotOk U <;> simp_all

theorem callSlotsOf_one (T : Ty) :
    callSlotsOf [("c0", optTy T)] = if callSlotOk T then some [T] else none := by
  have hl : slotLabels "c" 1 = ["c0"] := by decide
  simp only [callSlotsOf, callSlotOf, optTy, List.length_cons, List.length_nil, List.map, hl,
    Kernel.Bounds.callsMax, List.mapM, List.mapM.loop]
  split <;> cases h : callSlotOk T <;> simp_all

theorem callSlotsOf_ok : ∀ {row : List (Label × Ty)} {ks : List Ty},
    row.mapM (fun e => callSlotOf e.2) = some ks → ∀ k ∈ ks, callSlotOk k = true
  | [], ks, h => by simp at h; subst h; simp
  | (l, t) :: row, ks, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨T, hT, ks', hks', rfl⟩ := h
    intro k hk
    cases hk with
    | head =>
      unfold callSlotOf at hT
      split at hT
      · split at hT
        · rename_i hok; cases hT; exact hok
        · cases hT
      · cases hT
    | tail _ hk => exact callSlotsOf_ok hks' k hk

theorem methodSig_slots {S t : Ty} {rels : List (Label × RelDecl)} {sg : Sig}
    (h : methodSig S rels t = some sg) : ∀ k ∈ sg.calls, callSlotOk k = true := by
  unfold methodSig at h
  split at h
  · split at h
    · split at h
      · rename_i ks es rs ps hks hes hrs
        split at h
        · cases h
          unfold callSlotsOf at hks
          split at hks
          · exact callSlotsOf_ok hks
          · cases hks
        · cases h
      · cases h
    · cases h
  · cases h

theorem resolveMethod_spec {p : Package} {method : Nat} {ℓ : Label} {sg : Sig}
    (h : resolveMethod (D := D) p method = .ok (ℓ, sg)) :
    ∃ mty, Row.find? ℓ (recordRow p.iface) = some mty ∧ methodSig p.state p.rels mty = some sg := by
  unfold resolveMethod at h
  simp only [pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, by assumption, by assumption⟩

/-! ## The deployed run -/

theorem sublist_map_inv {α β : Type} {f : α → β} : ∀ {l : List β} {l2 : List α}, l.Sublist (l2.map f) →
    ∃ l' : List α, l'.Sublist l2 ∧ l = l'.map f
  | l, [], h => by simp only [List.map_nil, List.sublist_nil] at h; subst h; exact ⟨[], .slnil, rfl⟩
  | l, a :: l2, h => by
    simp only [List.map_cons] at h
    cases h with
    | cons _ h => obtain ⟨l', h1, rfl⟩ := sublist_map_inv h; exact ⟨l', h1.cons _, rfl⟩
    | cons_cons _ h => obtain ⟨l', h1, rfl⟩ := sublist_map_inv h; exact ⟨a :: l', h1.cons_cons _, rfl⟩

/-- **Each call a method makes is in its own declared slot**: the calls of the deployed run match,
in order and one to one, a sublist of the resolved method's call slot types, each call of a kind
its slot names. So a method makes at most as many calls as it declares slots, and never two from
one slot (the run's result is typed by `invoke_never_stuck`, the calls row conforms by
`extract_conforms`, and `callsOf_go_kinds` reads it). Exercised with calls by journey LC0–LC4 and LC6. -/
theorem runMeasured_kinds {rc : Lang.ReceiptCheck} {bytesOf : D → ByteArray}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasured bytesOf digestOf rc look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ (ℓ : Label) (sg : Sig) (L : Loaded) (g : Nat) (p : Package),
      load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧ L.pkgs[g]? = some p ∧
      resolveMethod (D := D) p method = .ok (ℓ, sg) ∧
      ∃ ks', ks'.Sublist sg.calls ∧
        Matched (fun b k => ∃ arms, k = .sum arms ∧ b.kindName ∈ arms.map Prod.fst) calls ks' := by
  unfold runMeasured runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, hr0, hl, hp, hres, hst, hargs, -, hrows, rfl⟩ := runSetup_spec hS
  simp only at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -, -, -⟩ := h
  obtain ⟨mty, hm, hA⟩ := resolveMethod_spec hres
  have hok := invoke_never_stuck (ticks := budget) hl hp hm hA hst hargs hrows hr0
  rw [‹run _ _ _ _ _ = .value _ _›] at hok
  have hcf := extract_conforms (load_libTy hl).1 _ hok ‹(Machine.mk _).extract _ _ _ = Except.ok _›
  have hks := methodSig_slots hA
  refine ⟨ℓ, sg, L, g, p, hl, hp, hres, ?_⟩
  cases hcf with
  | record hrow =>
    cases hrow with
    | cons hcalls _ =>
      cases hcalls with
      | record hcs =>
        obtain ⟨ts, hts, hf⟩ := callsOf_go_kinds (by simp [slotLabels]) hcs hks ‹callsOf.go _ _ _ = Except.ok _›
        have hsnd : ((slotLabels "c" sg.calls.length).zip (sg.calls.map optTy)).map Prod.snd = sg.calls.map optTy :=
          List.map_snd_zip (by simp [slotLabels])
        rw [hsnd] at hts
        obtain ⟨ks', hks', rfl⟩ := sublist_map_inv hts
        refine ⟨ks', hks', ?_⟩
        refine Matched.map_right (fun b k hk => ?_) hf
        obtain ⟨arms, he, hmem⟩ := hk
        simp only [optTy, Ty.sum.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at he
        exact ⟨arms, he, hmem⟩

/-- A run makes at most as many calls as the resolved method declares slots. -/
theorem runMeasured_calls_le {rc : Lang.ReceiptCheck} {bytesOf : D → ByteArray}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasured bytesOf digestOf rc look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ (ℓ : Label) (sg : Sig) (L : Loaded) (g : Nat) (p : Package),
      load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧ L.pkgs[g]? = some p ∧
      resolveMethod (D := D) p method = .ok (ℓ, sg) ∧ calls.length ≤ sg.calls.length := by
  obtain ⟨ℓ, sg, L, g, p, hl, hp, hres, ks', hsub, hf⟩ := runMeasured_kinds h
  exact ⟨ℓ, sg, L, g, p, hl, hp, hres, hf.length_eq ▸ hsub.length_le⟩

end Nanodregg.Lang
