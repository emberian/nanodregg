/-
# Lang.Proofs.Provenance — every id a run holds entered where ids enter (LANG-41)

No primitive makes a digest (LANG-38): `deq` consumes two, `cat` and `beq` take bytes, and the
machine copies values, never builds one of type `digest`. So the digests a run returns, and every
digest extraction forces, are digests the run was GIVEN. `ValLits P` says every digest a value
holds, and every id literal and every value of each closure, suspension and knot inside it,
satisfies `P`; one step keeps it (`step_lits`), so a run (`run_lits`), a forced suspension
(`force_lits`) and an extraction (`extract_lits`) keep it. Nothing about `P` is assumed: it is any
property the environment's digests and the library's id literals have.

At the deployed method run (`runSetup`, the front half of `runMeasured`) this names the sources
(`runSetup_sources`, cv 01a14acf-a188): every digest of the extracted result is a member or object
id of the request (`agent`, `principal`, `self`), a digest of the arguments, a digest of the state
the World held, or an id literal of the loaded closure. Each source is checked where it enters:
the arguments and the state by `digestOf` (`runSetup`), the literals at every load (`checkLits`,
`load_lits`), and the request's ids are the World's own (`bytesOf` of a `D`). So, for a World whose
codec reads its own ids back (`hdig`), every digest of the result is accepted
(`runSetup_accepted`), and `callsOf`'s `not a digest` refusal is unreachable: past extraction the
deployed run refuses only for state without bytes (`runMeasured_past_extraction`, cv
01a14af1-2132). Its tooth is journey LD5: a World whose codec refuses one member's own id (`hdig`
false) makes `callsOf` refuse that member named in a call, by name.
-/
import Lang.Proofs.CallLive
import Lang.Sim.Need
import Lang.Proofs.CallTeeth

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

section
variable (P : ByteArray → Prop)

/-- Every id literal of term `t` satisfies `P`. -/
def TermLits (t : Term) : Prop := ∀ b ∈ t.digestLits, P b

def RowLits (fs : List (Label × Term)) : Prop := ∀ f ∈ fs, TermLits P f.2

/-- Every digest value `v` holds, and every id literal and value of each closure, suspension and
knot inside it, satisfies `P`. -/
inductive ValLits : Val → Prop
  | nat (n : Nat) : ValLits (.nat n)
  | bool (b : Bool) : ValLits (.bool b)
  | bytes (s : ByteArray) : ValLits (.bytes s)
  | digest {s : ByteArray} : P s → ValLits (.digest s)
  | clo {body : Term} {env : List Val} : TermLits P body → (∀ v ∈ env, ValLits v) →
      ValLits (.clo body env)
  | record {fs : List (Label × (Term × List Val))} : (∀ f ∈ fs, TermLits P f.2.1) →
      (∀ f ∈ fs, ∀ v ∈ f.2.2, ValLits v) → ValLits (.record fs)
  | knot {body : Term} {env : List Val} : TermLits P body → (∀ v ∈ env, ValLits v) →
      ValLits (.knot body env)
  | inj (ℓ : Label) {v : Val} : ValLits v → ValLits (.inj ℓ v)

def EnvLits (env : Env) : Prop := ∀ v ∈ env, ValLits P v

def FrameLits : Frame → Prop
  | .appL a env => TermLits P a ∧ EnvLits P env
  | .appR fn => ValLits P fn
  | .fix | .get _ | .inj _ => True
  | .primL _ b env => TermLits P b ∧ EnvLits P env
  | .primR _ a => ValLits P a
  | .extend fs env | .case fs env => RowLits P fs ∧ EnvLits P env
  | .ite a b env => TermLits P a ∧ TermLits P b ∧ EnvLits P env

def ControlLits : Control → Prop
  | .eval t env => TermLits P t ∧ EnvLits P env
  | .ret v => ValLits P v

def StateLits (s : State) : Prop := ControlLits P s.control ∧ ∀ f ∈ s.stack, FrameLits P f

def LibLits (lib : List Term) : Prop := ∀ t ∈ lib, TermLits P t

def StepLits : Step → Prop
  | .next s => StateLits P s
  | .halt v => ValLits P v
  | .fault _ => True

/-! ## Terms: a constructor's literals are its children's -/

theorem rowLits_of : ∀ {fs : List (Label × Term)}, (∀ b ∈ Term.rowDigestLits fs, P b) → RowLits P fs
  | [], _ => by simp [RowLits]
  | (ℓ, t) :: fs, h => by
    simp only [Term.rowDigestLits, List.mem_append] at h
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact fun b hb => h b (.inl hb)
    · exact rowLits_of (fun b hb => h b (.inr hb)) f hf

theorem tl_lam {A : Ty} {b : Term} (h : TermLits P (.lam A b)) : TermLits P b := by
  simpa [TermLits, Term.digestLits] using h

theorem tl_fix {t : Term} (h : TermLits P (.fix t)) : TermLits P t := by
  simpa [TermLits, Term.digestLits] using h

theorem tl_get {t : Term} {ℓ : Label} (h : TermLits P (.get t ℓ)) : TermLits P t := by
  simpa [TermLits, Term.digestLits] using h

theorem tl_inj {A : Ty} {ℓ : Label} {t : Term} (h : TermLits P (.inj A ℓ t)) : TermLits P t := by
  simpa [TermLits, Term.digestLits] using h

theorem tl_app {f a : Term} (h : TermLits P (.app f a)) : TermLits P f ∧ TermLits P a := by
  simp only [TermLits, Term.digestLits, List.mem_append] at h
  exact ⟨fun b hb => h b (.inl hb), fun b hb => h b (.inr hb)⟩

theorem tl_prim {p : Prim} {a b : Term} (h : TermLits P (.prim p a b)) : TermLits P a ∧ TermLits P b := by
  simp only [TermLits, Term.digestLits, List.mem_append] at h
  exact ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩

theorem tl_record {fs : List (Label × Term)} (h : TermLits P (.record fs)) : RowLits P fs := by
  simp only [TermLits, Term.digestLits] at h
  exact rowLits_of P h

theorem tl_extend {t : Term} {fs : List (Label × Term)} (h : TermLits P (.extend t fs)) :
    TermLits P t ∧ RowLits P fs := by
  simp only [TermLits, Term.digestLits, List.mem_append] at h
  exact ⟨fun x hx => h x (.inl hx), rowLits_of P fun x hx => h x (.inr hx)⟩

theorem tl_case {t : Term} {fs : List (Label × Term)} (h : TermLits P (.case t fs)) :
    TermLits P t ∧ RowLits P fs := by
  simp only [TermLits, Term.digestLits, List.mem_append] at h
  exact ⟨fun x hx => h x (.inl hx), rowLits_of P fun x hx => h x (.inr hx)⟩

theorem tl_ite {c a b : Term} (h : TermLits P (.ite c a b)) :
    TermLits P c ∧ TermLits P a ∧ TermLits P b := by
  simp only [TermLits, Term.digestLits, List.mem_append] at h
  exact ⟨fun x hx => h x (.inl (.inl hx)), fun x hx => h x (.inl (.inr hx)), fun x hx => h x (.inr hx)⟩

/-! ## One step keeps every id where it came from -/

theorem frames_cons {f : Frame} {k : List Frame} (hf : FrameLits P f) (hk : ∀ g ∈ k, FrameLits P g) :
    ∀ g ∈ f :: k, FrameLits P g := by
  intro g hg
  simp only [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact hf
  · exact hk g hg

theorem env_cons {v : Val} {env : Env} (hv : ValLits P v) (he : EnvLits P env) : EnvLits P (v :: env) := by
  intro w hw
  simp only [List.mem_cons] at hw
  rcases hw with rfl | hw
  · exact hv
  · exact he w hw

theorem suspend_lits {env : Env} {fs : List (Label × Term)} (he : EnvLits P env) (hf : RowLits P fs) :
    ValLits P (.record (suspend env fs)) := by
  refine .record (fun f hm => ?_) (fun f hm => ?_)
  · simp only [suspend, List.mem_map] at hm
    obtain ⟨g, hg, rfl⟩ := hm
    exact hf g hg
  · simp only [suspend, List.mem_map] at hm
    obtain ⟨g, hg, rfl⟩ := hm
    exact he

theorem mem_put {α : Type} {ℓ : Label} {a : α} {x : Label × α} :
    ∀ {xs : List (Label × α)}, x ∈ Row.put ℓ a xs → x = (ℓ, a) ∨ x ∈ xs
  | [], h => by simpa [Row.put] using h
  | (k, b) :: rest, h => by
    simp only [Row.put] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons.2 h)
    · split at h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · subst h; exact .inr (List.mem_cons_self ..)
        · rcases mem_put h with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_merge {α : Type} {x : Label × α} :
    ∀ {base over : List (Label × α)}, x ∈ Row.merge base over → x ∈ base ∨ x ∈ over
  | base, [], h => by simpa [Row.merge] using h
  | base, (ℓ, a) :: rest, h => by
    simp only [Row.merge] at h
    rcases mem_merge h with h | h
    · rcases mem_put h with rfl | h
      · exact .inr (List.mem_cons_self ..)
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

theorem primEval_lits {p : Prim} {a b r : Val} (h : primEval p a b = .ok r) : ValLits P r := by
  unfold primEval at h
  split at h <;> (try unfold natResult at h) <;> (repeat' split at h) <;>
    first | (cases h; constructor) | (simp at h)

theorem step_lits {lib : List Term} {s : State} (hlib : LibLits P lib) (hs : StateLits P s) :
    StepLits P (step lib s) := by
  obtain ⟨c, k, d⟩ := s
  obtain ⟨hc, hk⟩ := hs
  cases c with
  | eval t env =>
    obtain ⟨ht, he⟩ := hc
    cases t with
    | var i =>
      simp only [step]
      split
      · rename_i v hv; exact ⟨he v (List.mem_of_getElem? hv), hk⟩
      · trivial
    | lam A b => exact ⟨.clo (tl_lam P ht) he, hk⟩
    | app f a =>
      obtain ⟨h1, h2⟩ := tl_app P ht
      exact ⟨⟨h1, he⟩, frames_cons P ⟨h2, he⟩ hk⟩
    | fix t => exact ⟨⟨tl_fix P ht, he⟩, frames_cons P trivial hk⟩
    | nat n => exact ⟨.nat n, hk⟩
    | bool b => exact ⟨.bool b, hk⟩
    | bytes b => exact ⟨.bytes b, hk⟩
    | digest b => exact ⟨.digest (ht b (by simp [Term.digestLits])), hk⟩
    | prim p a b =>
      obtain ⟨h1, h2⟩ := tl_prim P ht
      exact ⟨⟨h1, he⟩, frames_cons P ⟨h2, he⟩ hk⟩
    | record fs => exact ⟨suspend_lits P he (tl_record P ht), hk⟩
    | get t ℓ => exact ⟨⟨tl_get P ht, he⟩, frames_cons P trivial hk⟩
    | extend t fs =>
      obtain ⟨h1, h2⟩ := tl_extend P ht
      exact ⟨⟨h1, he⟩, frames_cons P ⟨h2, he⟩ hk⟩
    | inj A ℓ t => exact ⟨⟨tl_inj P ht, he⟩, frames_cons P trivial hk⟩
    | case t arms =>
      obtain ⟨h1, h2⟩ := tl_case P ht
      exact ⟨⟨h1, he⟩, frames_cons P ⟨h2, he⟩ hk⟩
    | ite c a b =>
      obtain ⟨h1, h2, h3⟩ := tl_ite P ht
      exact ⟨⟨h1, he⟩, frames_cons P ⟨h2, h3, he⟩ hk⟩
    | ref i =>
      simp only [step]
      split
      · rename_i body hb
        exact ⟨⟨hlib body (List.mem_of_getElem? hb), by simp [EnvLits]⟩, hk⟩
      · trivial
  | ret v =>
    cases k with
    | nil => exact hc
    | cons f k =>
      have hf := hk f (List.mem_cons_self ..)
      have hk' : ∀ g ∈ k, FrameLits P g := fun g hg => hk g (List.mem_cons_of_mem _ hg)
      cases f with
      | appL a env => exact ⟨hf, frames_cons P hc hk'⟩
      | appR fn =>
        cases fn with
        | clo body cenv =>
          cases hf with
          | clo hb hce => exact ⟨⟨hb, env_cons P hc hce⟩, hk'⟩
        | _ => trivial
      | fix =>
        cases v with
        | clo body cenv =>
          cases hc with
          | clo hb hce => exact ⟨.knot hb hce, hk'⟩
        | _ => trivial
      | primL p b env => exact ⟨hf, frames_cons P hc hk'⟩
      | primR p a =>
        simp only [step]
        split
        · rename_i r hr; exact ⟨primEval_lits P hr, hk'⟩
        · trivial
      | get ℓ =>
        cases v with
        | record fs =>
          simp only [step]
          split
          · rename_i t env hfind
            cases hc with
            | record h1 h2 =>
              have hm := find?_mem hfind
              exact ⟨⟨h1 _ hm, h2 _ hm⟩, hk'⟩
          · trivial
        | knot body env =>
          cases hc with
          | knot hb hke => exact ⟨⟨hb, env_cons P (.knot hb hke) hke⟩, frames_cons P trivial hk'⟩
        | _ => trivial
      | extend fs env =>
        cases v with
        | record gs =>
          obtain ⟨hfs, he⟩ := hf
          cases hc with
          | record h1 h2 =>
            have hs := suspend_lits P he hfs
            cases hs with
            | record s1 s2 =>
              refine ⟨.record (fun x hx => ?_) (fun x hx => ?_), hk'⟩
              · rcases mem_merge hx with hx | hx
                · exact h1 x hx
                · exact s1 x hx
              · rcases mem_merge hx with hx | hx
                · exact h2 x hx
                · exact s2 x hx
        | knot body kenv =>
          cases hc with
          | knot hb hke => exact ⟨⟨hb, env_cons P (.knot hb hke) hke⟩, frames_cons P hf hk'⟩
        | _ => trivial
      | inj ℓ => exact ⟨.inj ℓ hc, hk'⟩
      | case arms env =>
        cases v with
        | inj ℓ w =>
          simp only [step]
          split
          · rename_i body hfind
            cases hc with
            | inj _ hw => exact ⟨⟨hf.1 _ (find?_mem hfind), env_cons P hw hf.2⟩, hk'⟩
          · trivial
        | _ => trivial
      | ite a b env =>
        cases v with
        | bool c =>
          cases c
          · exact ⟨⟨hf.2.1, hf.2.2⟩, hk'⟩
          · exact ⟨⟨hf.1, hf.2.2⟩, hk'⟩
        | _ => trivial

/-! ## Runs, forcing, extraction -/

theorem init_lits {t : Term} {env : Env} (ht : TermLits P t) (he : EnvLits P env) :
    StateLits P (State.init t env) :=
  ⟨⟨ht, he⟩, by simp [State.init]⟩

theorem run_lits {lib : List Term} {cap : Nat} (hlib : LibLits P lib) :
    ∀ (n u : Nat) (s : State) {v : Val} {used : Nat},
      StateLits P s → run lib cap n u s = .value v used → ValLits P v
  | 0, _, _, _, _, _, h => by simp [run] at h
  | n + 1, u, s, v, used, hs, h => by
    have hst := step_lits P hlib hs
    simp only [run] at h
    cases e : step lib s with
    | halt w =>
      rw [e] at hst
      simp only [e] at h
      simp only [Outcome.value.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hst
    | fault f => simp [e] at h
    | next s' =>
      rw [e] at hst
      simp only [e] at h
      split at h
      · simp at h
      · exact run_lits hlib n (u + 1) s' hst h

theorem force_lits {m : Machine} (hlib : LibLits P m.lib) {fuel : Nat} {t : Term} {env : Env} {v : Val}
    {f : Nat} (ht : TermLits P t) (he : EnvLits P env) (h : m.force fuel t env = .ok (v, f)) : ValLits P v := by
  unfold Machine.force at h
  split at h
  · rename_i v' used hv
    cases h
    exact run_lits P hlib _ _ _ (init_lits P ht he) hv
  · cases h

/-- The suspensions of a record: each one's term and environment. -/
def ThunksLits (fs : List (Label × (Term × Env))) : Prop :=
  (∀ x ∈ fs, TermLits P x.2.1) ∧ ∀ x ∈ fs, EnvLits P x.2.2

theorem unknot_lits {m : Machine} (hlib : LibLits P m.lib) : ∀ {rounds fuel : Nat} {v : Val}
    {fs : List (Label × (Term × Env))} {f : Nat}, ValLits P v → m.unknot rounds fuel v = .ok (fs, f) →
    ThunksLits P fs
  | rounds, fuel, .record fs', fs, f, hv, h => by
    cases hv with
    | record h1 h2 => simp only [Machine.unknot] at h; cases h; exact ⟨h1, h2⟩
  | 0, fuel, .knot b env, fs, f, _, h => by simp [Machine.unknot] at h
  | k + 1, fuel, .knot b env, fs, f, hv, h => by
    cases hv with
    | knot hb he =>
      simp only [Machine.unknot] at h
      split at h
      · rename_i v' fuel' hf
        exact unknot_lits hlib (force_lits P hlib hb (env_cons P (.knot hb he) he) hf) h
      · cases h
  | _, _, .nat _, _, _, _, h => by simp [Machine.unknot] at h
  | _, _, .bool _, _, _, _, h => by simp [Machine.unknot] at h
  | _, _, .bytes _, _, _, _, h => by simp [Machine.unknot] at h
  | _, _, .digest _, _, _, _, h => by simp [Machine.unknot] at h
  | _, _, .clo _ _, _, _, _, h => by simp [Machine.unknot] at h
  | _, _, .inj _ _, _, _, _, h => by simp [Machine.unknot] at h

mutual
theorem extract_lits {m : Machine} (hlib : LibLits P m.lib) : ∀ (T : Ty) {fuel : Nat} {v : Val} {d : Data}
    {f : Nat}, ValLits P v → m.extract T fuel v = .ok (d, f) → ∀ b ∈ d.digests, P b
  | .nat, _, v, _, _, _, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h; simp [Data.digests]
  | .bool, _, v, _, _, _, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h; simp [Data.digests]
  | .bytes, _, v, _, _, _, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h; simp [Data.digests]
  | .digest, _, v, _, _, hv, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h
    cases hv with
    | digest hs => intro b hb; simp [Data.digests] at hb; subst hb; exact hs
  | .fn _ _, _, v, _, _, _, h => by cases v <;> simp [Machine.extract] at h
  | .record row, _, _, _, _, hv, h => by
    simp only [Machine.extract] at h
    split at h
    · rename_i fs fuel' hu
      split at h
      · rename_i ds fuel'' hr
        cases h
        intro b hb
        simp only [Data.digests] at hb
        exact extractRow_lits hlib row (unknot_lits P hlib hv hu) hr b hb
      · cases h
    · cases h
  | .sum row, _, v, _, _, hv, h => by
    cases v with
    | inj ℓ w =>
      cases hv with
      | inj _ hw =>
        simp only [Machine.extract] at h
        split at h
        · rename_i d' fuel' ha
          cases h
          intro b hb
          simp only [Data.digests] at hb
          exact extractArm_lits hlib row hw ha b hb
        · cases h
    | _ => simp [Machine.extract] at h

theorem extractArm_lits {m : Machine} (hlib : LibLits P m.lib) : ∀ (row : List (Label × Ty)) {ℓ : Label}
    {fuel : Nat} {w : Val} {d : Data} {f : Nat}, ValLits P w →
    m.extractArm row ℓ fuel w = .ok (d, f) → ∀ b ∈ d.digests, P b
  | [], _, _, _, _, _, _, h => by simp [Machine.extractArm] at h
  | (k, B) :: row, ℓ, _, _, _, _, hw, h => by
    simp only [Machine.extractArm] at h
    split at h
    · exact extract_lits hlib B hw h
    · exact extractArm_lits hlib row hw h

theorem extractRow_lits {m : Machine} (hlib : LibLits P m.lib) : ∀ (row : List (Label × Ty)) {fuel : Nat}
    {fs : List (Label × (Term × Env))} {ds : List (Label × Data)} {f : Nat},
    ThunksLits P fs → m.extractRow row fuel fs = .ok (ds, f) → ∀ b ∈ Data.rowDigests ds, P b
  | [], _, fs, _, _, _, h => by
    cases fs with
    | nil => simp only [Machine.extractRow] at h; cases h; simp [Data.rowDigests]
    | cons _ _ => simp [Machine.extractRow] at h
  | (ℓ, A) :: row, _, fs, _, _, ht, h => by
    cases fs with
    | nil => simp [Machine.extractRow] at h
    | cons x fs =>
      obtain ⟨ℓ', t, env⟩ := x
      obtain ⟨h1, h2⟩ := ht
      have hrest : ThunksLits P fs :=
        ⟨fun y hy => h1 y (List.mem_cons_of_mem _ hy), fun y hy => h2 y (List.mem_cons_of_mem _ hy)⟩
      simp only [Machine.extractRow] at h
      split at h
      · split at h
        · rename_i v fuel' hfo
          split at h
          · rename_i d fuel'' hx
            split at h
            · rename_i ds' f' hr
              cases h
              have hv := force_lits P hlib (h1 _ (List.mem_cons_self ..)) (h2 _ (List.mem_cons_self ..)) hfo
              intro b hb
              simp only [Data.rowDigests, List.mem_append] at hb
              rcases hb with hb | hb
              · exact extract_lits hlib A hv hx b hb
              · exact extractRow_lits hlib row hrest hr b hb
            · cases h
          · cases h
        · cases h
      · cases h
end

mutual
theorem toVal_lits : ∀ (d : Data), (∀ b ∈ d.digests, P b) → ValLits P d.toVal
  | .nat n, _ => .nat n
  | .bool b, _ => .bool b
  | .bytes s, _ => .bytes s
  | .digest s, h => .digest (h s (by simp [Data.digests]))
  | .record fs, h => by
    simp only [Data.toVal]
    simp only [Data.digests] at h
    obtain ⟨h1, h2⟩ := rowToVal_lits fs h
    exact .record h1 h2
  | .inj ℓ d, h => by
    simp only [Data.toVal]
    simp only [Data.digests] at h
    exact .inj ℓ (toVal_lits d h)

theorem rowToVal_lits : ∀ (fs : List (Label × Data)), (∀ b ∈ Data.rowDigests fs, P b) →
    ThunksLits P (Data.rowToVal fs)
  | [], _ => ⟨by simp [Data.rowToVal], by simp [Data.rowToVal]⟩
  | (ℓ, d) :: fs, h => by
    simp only [Data.rowDigests, List.mem_append] at h
    obtain ⟨h1, h2⟩ := rowToVal_lits fs fun b hb => h b (.inr hb)
    have hd := toVal_lits d fun b hb => h b (.inl hb)
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Data.rowToVal, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [TermLits, Term.digestLits]
      · exact h1 x hx
    · simp only [Data.rowToVal, List.mem_cons] at hx
      rcases hx with rfl | hx
      · intro v hv; simp at hv; subst hv; exact hd
      · exact h2 x hx
end

/-- **Provenance of a run's data**: a term with its id literals in `P`, run in an environment and a
library whose ids are all in `P`, to a value that extracts at any type: every digest of the data is
in `P`. -/
theorem run_extract_lits {lib : List Term} {t : Term} {env : Env} {budget used fuel left : Nat} {v : Val}
    {T : Ty} {d : Data} (hlib : LibLits P lib) (ht : TermLits P t) (he : EnvLits P env)
    (hr : run lib Bounds.stackMax budget 0 (State.init t env) = .value v used)
    (hx : (Machine.mk lib).extract T fuel v = .ok (d, left)) : ∀ b ∈ d.digests, P b :=
  extract_lits P (m := ⟨lib⟩) hlib T (run_lits P hlib _ _ _ (init_lits P ht he) hr) hx

end

/-! ## Where ids enter a method run -/

mutual
theorem relocate_digestLits (f : Nat → Nat) : ∀ t : Term, (t.relocate f).digestLits = t.digestLits
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ => by simp [Term.relocate, Term.digestLits]
  | .lam _ b => by simp [Term.relocate, Term.digestLits, relocate_digestLits f b]
  | .app g a => by simp [Term.relocate, Term.digestLits, relocate_digestLits f g, relocate_digestLits f a]
  | .fix t => by simp [Term.relocate, Term.digestLits, relocate_digestLits f t]
  | .prim _ a b => by simp [Term.relocate, Term.digestLits, relocate_digestLits f a, relocate_digestLits f b]
  | .record fs => by simp [Term.relocate, Term.digestLits, relocateRow_digestLits f fs]
  | .get t _ => by simp [Term.relocate, Term.digestLits, relocate_digestLits f t]
  | .extend t fs => by
    simp [Term.relocate, Term.digestLits, relocate_digestLits f t, relocateRow_digestLits f fs]
  | .inj _ _ t => by simp [Term.relocate, Term.digestLits, relocate_digestLits f t]
  | .case t fs => by
    simp [Term.relocate, Term.digestLits, relocate_digestLits f t, relocateRow_digestLits f fs]
  | .ite c a b => by
    simp [Term.relocate, Term.digestLits, relocate_digestLits f c, relocate_digestLits f a,
      relocate_digestLits f b]

theorem relocateRow_digestLits (f : Nat → Nat) :
    ∀ fs : List (Label × Term), Term.rowDigestLits (Term.relocateRow f fs) = Term.rowDigestLits fs
  | [] => by simp [Term.relocateRow, Term.rowDigestLits]
  | (_, t) :: fs => by
    simp [Term.relocateRow, Term.rowDigestLits, relocate_digestLits f t, relocateRow_digestLits f fs]
end

section
variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

theorem digestsOk_mem {ds : List ByteArray} (h : digestsOk digestOf ds = true) :
    ∀ b ∈ ds, (digestOf b).isSome = true := by
  unfold digestsOk at h
  exact fun b hb => List.all_eq_true.1 h b hb

theorem checkLits_lits {p : Package} {u : Unit} (h : checkLits digestOf p = .ok u) :
    ∀ b ∈ p.body.digestLits, (digestOf b).isSome = true := by
  unfold checkLits at h
  split at h
  · exact digestsOk_mem ‹_›
  · cases h

/-- The id literals of a closure's bodies are all accepted by `digestOf`. -/
def ClosureLits (digestOf : ByteArray → Option D) (L : Loaded) : Prop :=
  ∀ t ∈ L.lib, ∀ b ∈ t.digestLits, (digestOf b).isSome = true

theorem admitPackage_lits {idb : ByteArray} {p : Package} {acc L : Loaded} {gis : List Nat} {g : Nat}
    (hacc : ClosureLits digestOf acc) (h : admitPackage digestOf idb p acc gis = .ok (L, g)) :
    ClosureLits digestOf L := by
  unfold admitPackage at h
  cases h1 : ifacesAt acc.pkgs gis with
  | none => simp [h1] at h
  | some ifs =>
    cases h2 : p.checkWith ifs with
    | error e => simp [h1, h2] at h
    | ok u =>
      cases h3 : checkLits digestOf p with
      | error e => simp [h1, h2, h3] at h
      | ok u' =>
        simp only [h1, h2, h3, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro t ht b hb
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hacc t ht b hb
        · rw [relocate_digestLits] at hb
          exact checkLits_lits h3 b hb

section
variable (digestOf : ByteArray → Option D) (look : Pinned D)

mutual
/-- Every closure `load` builds holds only id literals `digestOf` accepts: each package passed
`checkLits` when it was admitted, and relocation keeps a body's literals. -/
theorem load_lits (fuel : Nat) (idb : ByteArray) (acc : Loaded) {L : Loaded} {g : Nat}
    (hacc : ClosureLits digestOf acc) (h : load digestOf look fuel idb acc = .ok (L, g)) :
    ClosureLits digestOf L := by
  unfold load at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hacc
  · split at h
    · simp at h
    · rename_i fuel
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i acc' gis hall
            exact admitPackage_lits (loadAll_lits fuel _ acc hacc hall) h
termination_by (fuel, 0)

theorem loadAll_lits (fuel : Nat) (ds : List ByteArray) (acc : Loaded) {L : Loaded} {gs : List Nat}
    (hacc : ClosureLits digestOf acc) (h : loadAll digestOf look fuel ds acc = .ok (L, gs)) :
    ClosureLits digestOf L := by
  unfold loadAll at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hacc
  · rename_i d ds
    split at h
    · simp at h
    · rename_i acc1 g1 h1
      split at h
      · simp at h
      · rename_i acc2 gs2 h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact loadAll_lits fuel ds acc1 (load_lits fuel d acc hacc h1) h2
termination_by (fuel, ds.length + 1)
end
end

theorem readState_go_digests {st : Kernel.Slots} : ∀ (row : List (Label × Ty)) (i : Nat) {d : Data},
    readState.go digestOf st row i = .ok d → ∀ b ∈ d.digests, (digestOf b).isSome = true
  | [], i, d, h => by
    simp only [readState.go, Except.ok.injEq] at h; subst h; simp [Data.digests, Data.rowDigests]
  | (ℓ, t) :: row, i, d, h => by
    simp only [readState.go] at h
    split at h
    · cases h
    · split at h
      · rename_i d' ds hd hg
        split at h
        · rename_i hok
          simp only [Except.ok.injEq] at h
          subst h
          have ih := readState_go_digests row (i + 1) hg
          intro b hb
          simp only [Data.digests, Data.rowDigests, List.mem_append] at hb ih
          rcases hb with hb | hb
          · exact digestsOk_mem hok b hb
          · exact ih b hb
        · cases h
      all_goals cases h

theorem readState_digests {row : List (Label × Ty)} {st : Kernel.Slots} {d : Data}
    (h : readState digestOf row st = .ok d) : ∀ b ∈ d.digests, (digestOf b).isSome = true :=
  readState_go_digests row 0 h

theorem occasionData_digests (o : Occasion D) : (occasionData bytesOf o).digests = [] := by
  cases o <;> simp [occasionData, Data.digests, Data.rowDigests]

/-- A request's digests are its member and object ids, and nothing of the occasion. -/
theorem reqData_digests (r : Req D) :
    (reqData bytesOf r).digests = [bytesOf r.agent, bytesOf r.principal, bytesOf r.self] := by
  simp [reqData, Data.digests, Data.rowDigests, occasionData_digests]

/-- Where a digest of a method run may come from: a member or object id of the request, a digest
of the arguments, a digest of the state the World held, or an id literal of the loaded closure. -/
def RunSource (bytesOf : D → ByteArray) (r : Req D) (S : RunSetup) (b : ByteArray) : Prop :=
  b = bytesOf r.agent ∨ b = bytesOf r.principal ∨ b = bytesOf r.self ∨
    b ∈ S.args.digests ∨ b ∈ S.state.digests ∨ ∃ t ∈ S.lib, b ∈ t.digestLits

theorem apply3_lits (P : ByteArray → Prop) (g : Nat) (ℓ : Label) : TermLits P (apply3 g ℓ) := by
  simp [TermLits, apply3, Term.digestLits]

theorem env3_lits (P : ByteArray → Prop) {x y z : Data} (hx : ∀ b ∈ x.digests, P b)
    (hy : ∀ b ∈ y.digests, P b) (hz : ∀ b ∈ z.digests, P b) : EnvLits P [x.toVal, y.toVal, z.toVal] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact toVal_lits P x hx
  · exact toVal_lits P y hy
  · exact toVal_lits P z hz

/-- **Digest provenance** (cv 01a14acf-a188): every digest of what a method run returns, at every
depth extraction reaches, is a member or object id of the request, a digest of the arguments, a
digest of the state, or an id literal of the closure (`RunSource`). The run makes none. -/
theorem runSetup_sources {look : Pinned D} {pkg : D} {state : Kernel.Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {S : RunSetup} {budget used fuel left : Nat} {v : Val} {d : Data}
    (hS : runSetup bytesOf digestOf look pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (d, left)) :
    ∀ b ∈ d.digests, RunSource bytesOf r S b := by
  obtain ⟨L, g, p, ℓ, A, ks, sd, ad, -, -, -, -, -, -, -, rfl⟩ := runSetup_spec hS
  refine run_extract_lits (RunSource bytesOf r _) (fun t ht b hb => ?_) (apply3_lits _ g ℓ) ?_ hr hx
  · exact .inr (.inr (.inr (.inr (.inr ⟨t, ht, hb⟩))))
  · refine env3_lits _ (fun b hb => ?_) (fun b hb => .inr (.inr (.inr (.inl hb))))
      (fun b hb => .inr (.inr (.inr (.inr (.inl hb)))))
    rw [reqData_digests] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))

/-- Every source is accepted where it entered: the arguments and the state by `runSetup`'s digest
checks, the closure's literals by `checkLits` at load, and the request's ids because they are the
World's own (`hdig`, the World's codec reads its ids back). So every digest a method run returns is
one `digestOf` accepts. -/
theorem runSetup_accepted (hdig : ∀ x, (digestOf (bytesOf x)).isSome = true) {look : Pinned D} {pkg : D}
    {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D} {S : RunSetup}
    {budget used fuel left : Nat} {v : Val} {d : Data}
    (hS : runSetup bytesOf digestOf look pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (d, left)) :
    ∀ b ∈ d.digests, (digestOf b).isSome = true := by
  have hsrc := runSetup_sources hS hr hx
  obtain ⟨L, g, p, ℓ, A, ks, sd, ad, -, hl, -, -, hst, -, hda, rfl⟩ := runSetup_spec hS
  have hlits := load_lits digestOf look _ _ _ (fun t ht => by simp at ht) hl
  intro b hb
  rcases hsrc b hb with rfl | rfl | rfl | h | h | ⟨t, ht, h⟩
  · exact hdig _
  · exact hdig _
  · exact hdig _
  · exact digestsOk_mem hda b h
  · exact readState_digests hst b h
  · exact hlits t ht b h

theorem mem_rowDigests {b : ByteArray} {ℓ : Label} {d : Data} :
    ∀ {fs : List (Label × Data)}, (ℓ, d) ∈ fs → b ∈ d.digests → b ∈ Data.rowDigests fs
  | [], h, _ => by simp at h
  | (k, e) :: fs, h, hb => by
    simp only [List.mem_cons, Prod.mk.injEq] at h
    simp only [Data.rowDigests, List.mem_append]
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .inl hb
    · exact .inr (mem_rowDigests h hb)

theorem digestAt_mem {b : ByteArray} {q : List Label} {d : Data} (h : DigestAt b q d) : b ∈ d.digests := by
  induction h with
  | here => simp [Data.digests]
  | inj _ ih => simpa [Data.digests] using ih
  | arm _ ih => simpa [Data.digests] using ih
  | field hm _ ih => simpa [Data.digests] using mem_rowDigests hm ih

/-- **`callsOf` never refuses a checked run** (cv 01a14af1-2132): for a World whose codec reads its
own ids back (`hdig`), once a method has run and its result has been extracted, the result is a
calls row and a state record, `callsOf` reads the calls, and the deployed run refuses only when the
state has no bytes at its type. So `calls: cI FIELD: not a digest` is unreachable from checked
Lang output: every digest of the calls is one the boundary or the World accepted
(`runSetup_accepted`), and a calls row of its type is refused only for a digest `digestOf` refuses
(`callsOf_live`). Tooth: journey LD5, where `hdig` fails for one member and `callsOf` refuses it. -/
theorem runMeasured_past_extraction (hdig : ∀ x, (digestOf (bytesOf x)).isSome = true) {look : Pinned D}
    {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat}
    {S : RunSetup} {used left : Nat} {v : Val} {d : Data}
    (hS : runSetup bytesOf digestOf look pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c : Data) (ds : List (Label × Data)) (calls : List (Body D)),
      d = .record [("calls", c), ("state", .record ds)] ∧ callsOf digestOf c = .ok calls ∧
      runMeasured bytesOf digestOf look pkg state method args r budget =
        match stateSlots S.row ds 0 with
        | some slots => .ok (slots, calls, budget - left, S.pkgs)
        | none => .error (.program s!"{S.label}: state bytes") := by
  have hacc := runSetup_accepted hdig hS hr hx
  have hS' := hS
  obtain ⟨L, g, p, ℓ, A, ks, sd, ad, hr0, hl, hp, hres, hst, hargs, -, rfl⟩ := runSetup_spec hS
  obtain ⟨mty, hm, hA⟩ := resolveMethod_spec hres
  have hok := invoke_never_stuck (ticks := budget) hl hp hm hA hst hargs hr0
  simp only at hr hx
  rw [hr] at hok
  have hcf := extract_conforms (load_libTy hl).1 (resultTy p.state ks) hok hx
  have hks := methodSig_slots hA
  have hstate := checkShape_state ((load_checked hl g p hp).1)
  cases hcf with
  | record hrow =>
    cases hrow with
    | cons hcalls hrest =>
      cases hrest with
      | cons hst' hnil =>
        cases hnil
        rw [hstate] at hst'
        cases hst' with
        | record hds =>
          rename_i c ds
          cases hc : callsOf digestOf c with
          | error e =>
            exfalso
            obtain ⟨ℓ', q, f, b, hn, hb, -, -⟩ := callsOf_live hks hcalls e hc
            have := hacc b (by simp only [Data.digests, Data.rowDigests, List.mem_append]; exact .inl (digestAt_mem hb))
            simp [hn] at this
          | ok calls =>
            refine ⟨c, ds, calls, rfl, hc, ?_⟩
            unfold runMeasured
            simp only [bind, Except.bind, hS', hr, hx]
            cases stateSlots (recordRow p.state) ds 0 <;> simp [hc, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
end


/-- The Sim's World meets `hdig` (its codec reads its own ids back, `sim_digest_roundtrip`), so
`runMeasured_past_extraction` holds there with no premise on the World: every admitted Sim run
past extraction reads its calls. -/
theorem sim_hdig (x : Kernel.Sim.D) : (Kernel.Sim.digestOf (Kernel.Sim.dc.bytes x)).isSome = true := by
  simp [Teeth.sim_digest_roundtrip]

theorem runMeasured_past_extraction_sim {look : Pinned Kernel.Sim.D} {pkg : Kernel.Sim.D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Req Kernel.Sim.D} {budget : Nat} {S : RunSetup} {used left : Nat}
    {v : Val} {d : Data}
    (hS : runSetup Kernel.Sim.dc.bytes Kernel.Sim.digestOf look pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c : Data) (ds : List (Label × Data)) (calls : List (Body Kernel.Sim.D)),
      d = .record [("calls", c), ("state", .record ds)] ∧ callsOf Kernel.Sim.digestOf c = .ok calls ∧
      runMeasured Kernel.Sim.dc.bytes Kernel.Sim.digestOf look pkg state method args r budget =
        match stateSlots S.row ds 0 with
        | some slots => .ok (slots, calls, budget - left, S.pkgs)
        | none => .error (.program s!"{S.label}: state bytes") :=
  runMeasured_past_extraction sim_hdig hS hr hx

/-! ## Teeth -/

private def catTerm : Term := .prim .cat (.bytes ⟨#[1]⟩) (.bytes ⟨#[2]⟩)

/-- `catTerm` has no id literal and runs in no environment: by `run_lits` (at `P := fun _ => False`)
its value holds no digest, and the deployed machine returns bytes. -/
theorem catTerm_bytes :
    (match run [] 8 16 0 (State.init catTerm) with
      | .value (.bytes b) _ => b.data == #[1, 2]
      | _ => false) = true := by decide

/-- The tooth of `step_lits`/`run_lits`: a stepper with a primitive that makes an id from bytes
(`Need.forgeStep`) returns a digest from the same literal-free term, so "no step makes a digest" is
a fact about the deployed step, and the plant refutes it. -/
theorem catTerm_forged :
    (match Need.runBy (Need.forgeStep []) 8 16 0 (State.init catTerm) with
      | .value (.digest b) _ => b.data == #[1, 2]
      | _ => false) = true := by decide

end Nanodregg.Lang
