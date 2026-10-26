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
the World held, a digest of the rows `readsData` built from the caller's view, or an id literal of
the loaded closure. Each source is checked where it enters:
the arguments and the state by `digestOf` (`runSetup`), the rows the caller's view gave by
`readsData`'s `checked` (`readsData_digests`), the literals at every load (`checkLits`,
`load_lits`), and the request's ids are the World's own (`bytesOf` of a `D`). So, for a World whose
codec reads its own ids back (a lawful `Ctx`, `Receive.Ctx.Lawful`, cv 01a14b28-7029), every digest
of the result is accepted (`runSetup_accepted`), and `callsOf`'s `not a digest` refusal is unreachable: past extraction the
deployed run reads its calls and then does exactly the state's slots (refused only for state
without bytes), `editsOf` and `guardEdits` (`runMeasured_past_extraction`, cv
01a14af1-2132), and `X.program.run` reads its calls when the program decodes with the `Ctx`'s own
codec (`program_run_past_extraction`). Its teeth: `sim_drop_not_lawful`, a decoder that drops a byte
is not lawful; and journey LD5, a program whose decoder refuses one member's own id (the `Ctx`'s
does not) makes `callsOf` refuse that member named in a call, by name. The law is discharged at the Sim (`sim_ctx_lawful`) and at the deployed
codec (`Receive.deployed_ctx_lawful`).
-/
import Lang.Proofs.CallLive
import Lang.Sim.Need
import Lang.Proofs.CallTeeth
import Kernel.Proofs.Lawful
import Codec.Deployed

import Lang.Proofs.LiveInvoke
import Lang.Proofs.LiveClosed

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
  | .primR _ a _ => ValLits P a
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
  split at h <;> (try unfold natResult at h) <;> (try unfold appended at h) <;> (repeat' split at h) <;>
    first | (cases h; constructor) | (simp at h)

theorem step_lits {lib : List Term} {s : State} (hlib : LibLits P lib) (hs : StateLits P s) :
    StepLits P (step lib s) := by
  obtain ⟨c, k, d⟩ := s
  obtain ⟨hc, hk⟩ := hs
  cases c with
  | eval t env =>
    obtain ⟨ht, he⟩ := hc
    cases t with
    | hole _ _ => trivial
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
    | refuse _ _ => simp only [step]; trivial
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
      | primR p a j =>
        simp only [step, primStep]
        split
        · exact ⟨hc, frames_cons P hf hk'⟩
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
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => by
    simp [Term.relocate, Term.digestLits]
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
  | .hole n σ => by
    simp [Term.relocate, Term.digestLits, relocateList_digestLits f σ]

theorem relocateList_digestLits (f : Nat → Nat) :
    ∀ ts : List Term, Term.listDigestLits (Term.relocateList f ts) = Term.listDigestLits ts
  | [] => rfl
  | t :: ts => by
    simp [Term.relocateList, Term.listDigestLits, relocate_digestLits f t, relocateList_digestLits f ts]

theorem relocateRow_digestLits (f : Nat → Nat) :
    ∀ fs : List (Label × Term), Term.rowDigestLits (Term.relocateRow f fs) = Term.rowDigestLits fs
  | [] => by simp [Term.relocateRow, Term.rowDigestLits]
  | (_, t) :: fs => by
    simp [Term.relocateRow, Term.rowDigestLits, relocate_digestLits f t, relocateRow_digestLits f fs]
end

section
variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : ReceiptCheck}

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


theorem admitContextual_lits {prepare : List Ty → Package → Except HoleRefusal Term}
    {idb : ByteArray} {p : Package} {acc L : Loaded} {gis : List Nat} {g : Nat}
    (hacc : ClosureLits digestOf acc)
    (h : admitContextual digestOf prepare idb p acc gis = .ok (L, g)) :
    ClosureLits digestOf L := by
  unfold admitContextual at h
  split at h
  · exact admitPackage_lits hacc h
  ·
    repeat' split at h
    all_goals first | (cases h; done) | skip
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro t ht b hb
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hacc t ht b hb
    · rw [relocate_digestLits] at hb
      exact checkLits_lits ‹_› b hb

section
variable (digestOf : ByteArray → Option D) (rc : ReceiptCheck) (look : Pinned D)
  (admit : ByteArray → Package → Loaded → List Nat → Except (Refusal D) (Loaded × Nat))

mutual
/-- Every closure `load` builds holds only id literals `digestOf` accepts: each package passed
`checkLits` when it was admitted, and relocation keeps a body's literals. -/
theorem loadUsing_lits (hadmit : ∀ {idb p acc gis L g}, ClosureLits digestOf acc →
    admit idb p acc gis = .ok (L, g) → ClosureLits digestOf L) (fuel : Nat) (idb : ByteArray) (acc : Loaded) {L : Loaded} {g : Nat}
    (hacc : ClosureLits digestOf acc) (h : loadUsing digestOf admit look fuel idb acc = .ok (L, g)) :
    ClosureLits digestOf L := by
  unfold loadUsing at h
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
            exact hadmit (loadAllUsing_lits hadmit fuel _ acc hacc hall) h
termination_by (fuel, 0)

theorem loadAllUsing_lits (hadmit : ∀ {idb p acc gis L g}, ClosureLits digestOf acc →
    admit idb p acc gis = .ok (L, g) → ClosureLits digestOf L) (fuel : Nat) (ds : List ByteArray) (acc : Loaded) {L : Loaded} {gs : List Nat}
    (hacc : ClosureLits digestOf acc) (h : loadAllUsing digestOf admit look fuel ds acc = .ok (L, gs)) :
    ClosureLits digestOf L := by
  unfold loadAllUsing at h
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
        exact loadAllUsing_lits hadmit fuel ds acc1 (loadUsing_lits hadmit fuel d acc hacc h1) h2
termination_by (fuel, ds.length + 1)
end

end

section
variable (digestOf : ByteArray → Option D) (rc : ReceiptCheck) (look : Pinned D)

mutual
/-- Every closure `load` builds holds only id literals `digestOf` accepts: each package passed
`checkLits` when it was admitted, and relocation keeps a body's literals. -/
theorem load_lits (fuel : Nat) (idb : ByteArray) (acc : Loaded) {L : Loaded} {g : Nat}
    (hacc : ClosureLits digestOf acc) (h : load digestOf look fuel idb acc = .ok (L, g)) :
    ClosureLits digestOf L := by
  unfold load loadUsing at h
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
  unfold loadAll loadAllUsing at h
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

/-! ### The rows a run reads: every digest in them passed `checked` (LANG-49)

`readsData` builds the rows argument from the caller's `RowView`; each key, prefix and value it
places there entered through `checked digestOf`, and the slots and records around them hold no
digest. So the rows are a source exactly like the arguments and the state. -/

theorem rowDigests_append : ∀ (a b : List (Label × Data)),
    Data.rowDigests (a ++ b) = Data.rowDigests a ++ Data.rowDigests b
  | [], _ => by simp [Data.rowDigests]
  | (_, d) :: a, b => by simp [Data.rowDigests, rowDigests_append a b]

theorem checked_digests {what : String} {d d' : Data} (h : checked digestOf what d = .ok d') :
    ∀ b ∈ d'.digests, (digestOf b).isSome = true := by
  unfold checked at h
  split at h
  · rename_i hall
    cases h
    exact fun b hb => List.all_eq_true.1 hall b hb
  · cases h

theorem valOf_digests {dl : RelDecl} {what : String} {b : ByteArray} {v : Data}
    (h : valOf digestOf dl what b = .ok v) : ∀ x ∈ v.digests, (digestOf x).isSome = true := by
  unfold valOf at h
  split at h
  · exact checked_digests h
  · cases h

theorem optD_digests {o : Option Data}
    (h : ∀ x, o = some x → ∀ b ∈ x.digests, (digestOf b).isSome = true) :
    ∀ b ∈ (optD o).digests, (digestOf b).isSome = true := by
  cases o with
  | none => simp [optD, Data.digests, Data.rowDigests]
  | some x => simpa [optD, Data.digests] using h x rfl

theorem zipIdx_slots_digests {xs : List Data}
    (hx : ∀ x ∈ xs, ∀ b ∈ x.digests, (digestOf b).isSome = true) :
    ∀ (L : List Label) (k : Nat),
      ∀ b ∈ Data.rowDigests ((L.zipIdx k).map fun p => (p.1, optD xs[p.2]?)), (digestOf b).isSome = true
  | [], _ => by simp [Data.rowDigests]
  | l :: L, k => by
    simp only [List.zipIdx_cons, List.map_cons, Data.rowDigests, List.mem_append]
    rintro b (hb | hb)
    · exact optD_digests (fun x hx' => hx x (List.mem_of_getElem? hx')) b hb
    · exact zipIdx_slots_digests hx L (k + 1) b hb

theorem slotsD_digests {xs : List Data} (hx : ∀ x ∈ xs, ∀ b ∈ x.digests, (digestOf b).isSome = true)
    (c : String) (n : Nat) : ∀ b ∈ Data.rowDigests (slotsD c n xs), (digestOf b).isSome = true :=
  zipIdx_slots_digests hx _ 0

/-- **Every digest of a range read's rows is one `digestOf` accepted** (PROTOCOL-51): each key and
value `rangeRowData` builds passed `checked`. -/
theorem rangeRowData_digests {ℓ : Label} {dl : RelDecl} {rows : List (RowSlot D × RowLeaf)}
    {ds : List Data} (h : rangeRowData digestOf ℓ dl rows = .ok ds) :
    ∀ y ∈ ds, ∀ b ∈ y.digests, (digestOf b).isSome = true := by
  unfold rangeRowData at h
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_ok_mem h y hy
  simp only [bind, Except.bind, pure, Except.pure] at hq
  repeat' split at hq
  all_goals first | cases hq | skip
  all_goals
    simp only [Data.digests, Data.rowDigests, List.append_nil, List.mem_append]
    rintro z (hz | hz)
    · exact checked_digests ‹_› z hz
    · exact valOf_digests ‹_› z hz

/-- A read key's columns hold only accepted digests (CLIENT-35): `live` holds none, and the receipt
column's digests are those `receiptSeen` checked (E5). -/
theorem keyColumns_digests {rc : Lang.ReceiptCheck} {look : Pinned D} {ℓ : Label} {live receipt : Bool}
    {args k : Data} {cs : List (Label × Data)} (h : keyColumns digestOf rc look ℓ live receipt args k = .ok cs) :
    ∀ b ∈ Data.rowDigests cs, (digestOf b).isSome = true := by
  rcases keyColumns_ok h with ⟨-, -, rfl⟩ | ⟨-, -, -, g, -, -, -, -, rfl⟩ |
      ⟨-, -, g, -, -, s, -, -, -, -, -, hok, rfl⟩
  · simp [Data.rowDigests]
  · simp [Data.rowDigests, Data.digests]
  · have hall := List.all_eq_true.mp hok.2
    intro b hb
    rw [rowDigests_append] at hb
    cases live <;> simp only [Data.rowDigests, Data.digests, Bool.false_eq_true, if_false, if_true,
      List.nil_append, List.append_nil] at hb <;>
      exact hall b hb

/-- **A range read's rows with columns hold only accepted digests** (E5, CLIENT-35): the listed key
and value as `rangeRowData` checked them, and the columns' (`keyColumns_digests`). -/
theorem columnRows_digests {rc : Lang.ReceiptCheck} {look : Pinned D} {ℓ : Label} {live receipt : Bool}
    {args : Data} {rs ys : List Data} (hx : ∀ y ∈ rs, ∀ b ∈ y.digests, (digestOf b).isSome = true)
    (h : columnRows digestOf rc look ℓ live receipt args rs = .ok ys) :
    ∀ y ∈ ys, ∀ b ∈ y.digests, (digestOf b).isSome = true := by
  unfold columnRows at h
  by_cases hc : (live || receipt) = true
  · rw [if_pos hc] at h
    intro y hy
    obtain ⟨q, hq, hqy⟩ := mapM_ok_mem h y hy
    unfold columnRow at hqy
    split at hqy
    · rename_i k v
      split at hqy
      · cases hqy
      · rename_i cs hcs
        simp only [Except.ok.injEq] at hqy
        subst hqy
        have hq' := hx _ hq
        intro z hz
        simp only [Data.digests] at hz hq'
        rw [rowDigests_append, rowDigests_append] at hz
        simp only [Data.rowDigests, List.append_nil, List.mem_append] at hz hq'
        rcases hz with (hz | hz) | hz
        · exact hq' z (.inl hz)
        · exact keyColumns_digests hcs z hz
        · exact hq' z (.inr hz)
    · cases hqy
  · rw [if_neg hc] at h
    simp only [Except.ok.injEq] at h
    subst h; exact hx

theorem relReads_digests {look : Pinned D} {rv : RowView D} {self : D} {i : Nat} {ℓ : Label} {dl : RelDecl} {x : RelRead}
    {rc : Lang.ReceiptCheck} {args : Data}
    {v : Data} (h : relReads digestOf rc look rv self i ℓ dl x args = .ok v) :
    ∀ b ∈ v.digests, (digestOf b).isSome = true := by
  unfold relReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals
    simp only [Data.digests, rowDigests_append, List.mem_append]
    rintro b (hb | hb)
    · refine slotsD_digests (fun y hy => ?_) "p" _ b hb
      obtain ⟨q, -, hq⟩ := mapM_ok_mem ‹List.mapM _ (rv.points self i) = Except.ok _› y hy
      split at hq
      · cases hq
      · rename_i kv hkv
        obtain ⟨k, val⟩ := kv
        obtain ⟨k0, -, h2, hv⟩ := readPoint_ok hkv
        have hvd : ∀ z ∈ (optD val).digests, (digestOf z).isSome = true := optD_digests (fun w hw => by
          rcases hv with ⟨rfl, -⟩ | ⟨_, _, _, w', -, hw', rfl⟩
          · cases hw
          · cases hw; exact valOf_digests hw')
        rcases pointData_ok hq with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, -, rfl⟩ |
            ⟨-, b0, g0, c0, rb0, sn0, -, -, -, -, -, hs, rfl⟩
        · simp only [Data.digests, Data.rowDigests, List.append_nil, List.mem_append]
          rintro z (hz | hz)
          · exact checked_digests h2 z hz
          · exact hvd z hz
        · simp only [Data.digests, Data.rowDigests, List.append_nil, List.mem_append, List.nil_append]
          rintro z (hz | hz)
          · exact checked_digests h2 z hz
          · exact hvd z hz
        · have hall := List.all_eq_true.mp hs.2
          intro z hz
          cases hlv : x.live <;>
            simp only [hlv, Data.digests, Data.rowDigests, List.append_nil, List.mem_append, if_true,
              Bool.false_eq_true, if_false, List.nil_append, List.cons_append] at hz
          all_goals
            rcases hz with hz | hz | hz <;>
              first | exact checked_digests h2 z hz | exact hvd z hz | exact hall z hz | (simp at hz)
    · first
        | (simp [Data.digests, Data.rowDigests] at hb; done)
        | (simp only [Data.rowDigests, Data.digests, List.append_nil, List.mem_append] at hb
           rcases hb with hb | hb
           · exact checked_digests ‹_› b hb
           · exact slotsD_digests (fun y hy => columnRows_digests
               (rangeRowData_digests ‹rangeRowData _ _ _ _ = .ok _›) ‹columnRows _ _ _ _ _ _ _ _ = .ok _› y hy) "r" _ b hb)

/-- **Every digest of the rows a run reads is one `digestOf` accepted** (LANG-49): what `readsData`
builds from the caller's row view holds only keys, prefixes and values that passed `checked`. -/
theorem readsData_digests {look : Pinned D} {rels : List (Label × RelDecl)} {rv : RowView D} {self : D}
    {rc : Lang.ReceiptCheck} {args : Data}
    {rs : List (Label × RelRead)} {wd : Data} (h : readsData digestOf rc look rels rv self rs args = .ok wd) :
    ∀ b ∈ wd.digests, (digestOf b).isSome = true := by
  unfold readsData at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i fs hfs
    cases h
    intro b hb
    simp only [Data.digests] at hb
    suffices hall : ∀ y ∈ fs, ∀ b ∈ y.2.digests, (digestOf b).isSome = true by
      clear hfs
      induction fs with
      | nil => simp [Data.rowDigests] at hb
      | cons y fs ih =>
        simp only [Data.rowDigests, List.mem_append] at hb
        rcases hb with hb | hb
        · exact hall y (by simp) b hb
        · exact ih hb (fun z hz => hall z (by simp [hz]))
    intro y hy
    obtain ⟨a, -, ha⟩ := mapM_ok_mem hfs y hy
    repeat' split at ha
    all_goals first | (cases ha; done) | (cases ha; exact relReads_digests ‹_›)

theorem rowDigests_mem {b : ByteArray} : ∀ {fs : List (Label × Data)},
    b ∈ Data.rowDigests fs → ∃ y ∈ fs, b ∈ y.2.digests
  | [], h => by simp [Data.rowDigests] at h
  | y :: fs, h => by
    simp only [Data.rowDigests, List.mem_append] at h
    rcases h with h | h
    · exact ⟨y, by simp, h⟩
    · obtain ⟨z, hz, hb⟩ := rowDigests_mem h
      exact ⟨z, by simp [hz], hb⟩

theorem rowDigests_of_mem {b : ByteArray} : ∀ {fs : List (Label × Data)} {y : Label × Data},
    y ∈ fs → b ∈ y.2.digests → b ∈ Data.rowDigests fs
  | [], _, h, _ => by simp at h
  | z :: fs, y, h, hb => by
    simp only [Data.rowDigests, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl hb
    · exact .inr (rowDigests_of_mem h hb)

/-- **Every digest of a method's rows argument is one `digestOf` accepted** (LANG-49, PROT-6): its own
reads' and its peer reads', both `readsData`'s. -/
theorem methodReads_digests {bytesOf : D → ByteArray} {rc : Lang.ReceiptCheck} {look : Pinned D} {pkg : D}
    {rels : List (Label × RelDecl)} {rv : RowView D} {self : D} {args : Data}
    {rs ps : List (Label × RelRead)} {wd : Data}
    (h : methodReads bytesOf digestOf rc look pkg rels rv self args rs ps = .ok wd) :
    ∀ b ∈ wd.digests, (digestOf b).isSome = true := by
  unfold methodReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i own hown
    cases ps with
    | nil => cases h; exact readsData_digests hown
    | cons q qs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
      cases hpo : peerOf bytesOf digestOf self args with
      | error e => rw [hpo] at h; cases h
      | ok peer =>
        rw [hpo] at h
        simp only at h
        cases hk : readKind look peer kindObject with
        | error e => rw [hk] at h; cases h
        | ok cell =>
          rw [hk] at h
          simp only at h
          by_cases hc : (cell.slots.get slotPackage == some (bytesOf pkg)) = true
          · simp only [hc, ↓reduceIte] at h
            cases hpd : readsData digestOf rc look rels rv peer (q :: qs) args with
            | error e => rw [hpd] at h; cases h
            | ok pd =>
              rw [hpd] at h
              simp only at h
              split at h
              · rename_i fs
                cases h
                intro b hb
                simp only [Data.digests] at hb
                obtain ⟨y, hy, hb⟩ := rowDigests_mem hb
                rw [(Row.sort_perm _).mem_iff] at hy
                rcases List.mem_append.mp hy with hy | hy
                · exact readsData_digests hown b (by simp only [Data.digests]; exact rowDigests_of_mem hy hb)
                · simp only [List.mem_singleton] at hy
                  subst hy
                  exact readsData_digests hpd b hb
              · cases h; exact readsData_digests hown
          · simp [hc] at h

/-- Where a digest of a method run may come from: a member or object id of the request, a digest
of the arguments, a digest of the state the World held, a digest of the rows `rows` the caller's
view gave (LANG-49), or an id literal of the loaded closure. -/
def RunSource (bytesOf : D → ByteArray) (r : Req D) (S : RunSetup) (rows : Data) (b : ByteArray) : Prop :=
  b = bytesOf r.agent ∨ b = bytesOf r.principal ∨ b = bytesOf r.self ∨
    b ∈ S.args.digests ∨ b ∈ S.state.digests ∨ b ∈ rows.digests ∨ ∃ t ∈ S.lib, b ∈ t.digestLits

theorem apply4_lits (P : ByteArray → Prop) (g : Nat) (ℓ : Label) : TermLits P (apply4 g ℓ) := by
  simp [TermLits, apply4, Term.digestLits]

theorem env4_lits (P : ByteArray → Prop) {x y z w : Data} (hx : ∀ b ∈ x.digests, P b)
    (hy : ∀ b ∈ y.digests, P b) (hz : ∀ b ∈ z.digests, P b) (hw : ∀ b ∈ w.digests, P b) :
    EnvLits P [x.toVal, y.toVal, z.toVal, w.toVal] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact toVal_lits P x hx
  · exact toVal_lits P y hy
  · exact toVal_lits P z hz
  · exact toVal_lits P w hw

/-- **Digest provenance** (cv 01a14acf-a188): every digest of what a method run returns, at every
depth extraction reaches, is a member or object id of the request, a digest of the arguments, a
digest of the state, a digest of the rows `readsData` built from the caller's view, or an id
literal of the closure (`RunSource`). The run makes none. -/
theorem runSetup_sources {rc : Lang.ReceiptCheck} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {S : RunSetup} {budget used fuel left : Nat} {v : Val} {d : Data}
    (hS : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (d, left)) :
    ∀ b ∈ d.digests, RunSource bytesOf r S S.reads b := by
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, -, -, -, -, -, -, hrows, rfl⟩ := runSetup_spec hS
  refine run_extract_lits (RunSource bytesOf r _ wd) (fun t ht b hb => ?_) (apply4_lits _ g ℓ) ?_ hr hx
  · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨t, ht, hb⟩)))))
  · refine env4_lits _ (fun b hb => ?_) (fun b hb => .inr (.inr (.inr (.inl hb))))
      (fun b hb => .inr (.inr (.inr (.inr (.inl hb)))))
      (fun b hb => .inr (.inr (.inr (.inr (.inr (.inl hb))))))
    rw [reqData_digests] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))

/-- Every source is accepted where it entered: the arguments and the state by `runSetup`'s digest
checks, the rows by `readsData`'s `checked` (`readsData_digests`), the closure's literals by
`checkLits` at load, and the request's ids because they are the World's own (`hdig`, the World's
codec reads its ids back). So every digest a method run returns is one `digestOf` accepts. -/
theorem runSetup_accepted_of {rc : Lang.ReceiptCheck} (hdig : ∀ x, (digestOf (bytesOf x)).isSome = true) {look : Pinned D}
    {rv : RowView D} {pkg : D}
    {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D} {S : RunSetup}
    {budget used fuel left : Nat} {v : Val} {d : Data}
    (hS : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (d, left)) :
    ∀ b ∈ d.digests, (digestOf b).isSome = true := by
  have hsrc := runSetup_sources hS hr hx
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, -, -, hst, -, hda, hrows, rfl⟩ := runSetup_spec hS
  have hlits := load_lits digestOf look _ _ _ (fun t ht => by simp at ht) hl
  intro b hb
  rcases hsrc b hb with rfl | rfl | rfl | h | h | h | ⟨t, ht, h⟩
  · exact hdig _
  · exact hdig _
  · exact hdig _
  · exact digestsOk_mem hda b h
  · exact readState_digests hst b h
  · exact methodReads_digests hrows b h
  · exact hlits t ht b h

theorem runSetupLive_sources {rc : Lang.ReceiptCheck} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {S : RunSetup} {budget used fuel left : Nat} {v : Val} {d : Data}
    (hS : runSetupLive bytesOf digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (d, left)) :
    ∀ b ∈ d.digests, RunSource bytesOf r S S.reads b := by
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, -, -, -, -, -, -, hrows, rfl⟩ := runSetupWith_spec hS
  refine run_extract_lits (RunSource bytesOf r _ wd) (fun t ht b hb => ?_) (apply4_lits _ g ℓ) ?_ hr hx
  · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨t, ht, hb⟩)))))
  · refine env4_lits _ (fun b hb => ?_) (fun b hb => .inr (.inr (.inr (.inl hb))))
      (fun b hb => .inr (.inr (.inr (.inr (.inl hb)))))
      (fun b hb => .inr (.inr (.inr (.inr (.inr (.inl hb))))))
    rw [reqData_digests] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))

/-- Every source is accepted where it entered: the arguments and the state by `runSetup`'s digest
checks, the rows by `readsData`'s `checked` (`readsData_digests`), the closure's literals by
`checkLits` at load, and the request's ids because they are the World's own (`hdig`, the World's
codec reads its ids back). So every digest a method run returns is one `digestOf` accepts. -/
theorem runSetupLive_accepted_of {rc : Lang.ReceiptCheck} (hdig : ∀ x, (digestOf (bytesOf x)).isSome = true) {look : Pinned D}
    {rv : RowView D} {pkg : D}
    {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D} {S : RunSetup}
    {budget used fuel left : Nat} {v : Val} {d : Data}
    (hS : runSetupLive bytesOf digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (d, left)) :
    ∀ b ∈ d.digests, (digestOf b).isSome = true := by
  have hsrc := runSetupLive_sources hS hr hx
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, -, -, hst, -, hda, hrows, rfl⟩ := runSetupWith_spec hS
  have hlits := loadUsing_lits digestOf look _ (fun ha hr => admitContextual_lits ha hr) _ _ _ (fun t ht => by simp at ht) hl
  intro b hb
  rcases hsrc b hb with rfl | rfl | rfl | h | h | h | ⟨t, ht, h⟩
  · exact hdig _
  · exact hdig _
  · exact hdig _
  · exact digestsOk_mem hda b h
  · exact readState_digests hst b h
  · exact methodReads_digests hrows b h
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
calls row, an edits row and a state record, `callsOf` reads the calls, and what the deployed run
does next is exactly: the state's slots (refused only when the state has no bytes at its type),
then the edits read into row acts (`editsOf`), then each edit judged by its relation's guard
(`guardEdits`). So `calls: cI FIELD: not a digest` is unreachable from checked Lang output: every
digest of the calls is one the boundary or the World accepted (`runSetup_accepted`), and a calls
row of its type is refused only for a digest `digestOf` refuses (`callsOf_live`). Tooth: journey
LD5, where `hdig` fails for one member and `callsOf` refuses it. -/
private theorem runMeasured_past_extraction_of {rc : Lang.ReceiptCheck} (hdig : ∀ x, (digestOf (bytesOf x)).isSome = true) {look : Pinned D}
    {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D}
    {budget : Nat} {S : RunSetup} {used left : Nat} {v : Val} {d : Data}
    (hS : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c e : Data) (ds : List (Label × Data)) (calls : List (Body D)),
      d = .record [("calls", c), ("edits", e), ("state", .record ds)] ∧ callsOf digestOf S.calls c = .ok calls ∧
      runMeasured bytesOf digestOf rc look rv pkg state method args r budget =
        match stateSlots S.row ds 0 with
        | some slots => do
            let es ← editsOf S.rels r.self e
            guardEdits bytesOf digestOf S rv pkg r es
            pure (slots, calls, es.map (fun x => (x.slot, x.act)), budget - left, S.pkgs)
        | none => .error (.program s!"{S.label}: state bytes") := by
  have hacc := runSetup_accepted_of hdig hS hr hx
  have hS' := hS
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, hr0, hl, hp, hres, hst, hargs, -, hrows, rfl⟩ := runSetup_spec hS
  obtain ⟨mty, hm, hA⟩ := resolveMethod_spec hres
  have hok := invoke_never_stuck (ticks := budget) hl hp hm hA hst hargs hrows hr0
  simp only at hr hx
  rw [hr] at hok
  have hcf := extract_conforms (load_libTy hl).1 (resultTy p.state sg.calls (editTy p.rels) sg.edits) hok hx
  have hks := methodSig_slots hA
  have hstate := checkShape_state ((load_checked hl g p hp).1)
  cases hcf with
  | record hrow =>
    cases hrow with
    | cons hcalls hrest =>
      cases hrest with
      | cons hed hrest2 =>
        cases hrest2 with
        | cons hst' hnil =>
          cases hnil
          rw [hstate] at hst'
          cases hst' with
          | record hds =>
            rename_i c e ds
            cases hc : callsOf digestOf sg.calls c with
            | error err =>
              exfalso
              obtain ⟨ℓ', q, f, b, hn, hb, -, -⟩ := callsOf_live hks hcalls err hc
              have := hacc b (by simp only [Data.digests, Data.rowDigests, List.mem_append]; exact .inl (digestAt_mem hb))
              simp [hn] at this
            | ok calls =>
              refine ⟨c, e, ds, calls, rfl, hc, ?_⟩
              unfold runMeasured runMeasuredWith
              simp only [bind, Except.bind, hS', Nat.not_lt_zero, if_false, Nat.sub_zero, hr, hx]
              cases stateSlots (recordRow p.state) ds 0 <;>
                simp [hc, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
private theorem runMeasuredLive_past_extraction_of {rc : Lang.ReceiptCheck} (hdig : ∀ x, (digestOf (bytesOf x)).isSome = true) {look : Pinned D}
    {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D}
    {budget : Nat} {S : RunSetup} {used left : Nat} {v : Val} {d : Data}
    (hS : runSetupLive bytesOf digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c e : Data) (ds : List (Label × Data)) (calls : List (Body D)),
      d = .record [("calls", c), ("edits", e), ("state", .record ds)] ∧ callsOf digestOf S.calls c = .ok calls ∧
      runMeasuredLive bytesOf digestOf rc look rv pkg state method args r (budget + S.preparation) =
        match stateSlots S.row ds 0 with
        | some slots => do
            let es ← editsOf S.rels r.self e
            guardEdits bytesOf digestOf S rv pkg r es
            pure (slots, calls, es.map (fun x => (x.slot, x.act)), budget + S.preparation - left, S.pkgs)
        | none => .error (.program s!"{S.label}: state bytes") := by
  have hacc := runSetupLive_accepted_of hdig hS hr hx
  have hS' := hS
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, hr0, hl, hp, hres, hst, hargs, -, hrows, rfl⟩ := runSetupWith_spec hS
  obtain ⟨mty, hm, hA⟩ := resolveMethod_spec hres
  have hok := invoke_live_never_stuck (ticks := budget) hl hp hm hA hst hargs hrows hr0
  simp only at hr hx
  rw [hr] at hok
  have hcf := extract_conforms (loadLive_libTy hl).1 (resultTy p.state sg.calls (editTy p.rels) sg.edits) hok hx
  have hks := methodSig_slots hA
  have hstate := checkShape_state ((loadLive_checked hl g p hp).1)
  cases hcf with
  | record hrow =>
    cases hrow with
    | cons hcalls hrest =>
      cases hrest with
      | cons hed hrest2 =>
        cases hrest2 with
        | cons hst' hnil =>
          cases hnil
          rw [hstate] at hst'
          cases hst' with
          | record hds =>
            rename_i c e ds
            cases hc : callsOf digestOf sg.calls c with
            | error err =>
              exfalso
              obtain ⟨ℓ', q, f, b, hn, hb, -, -⟩ := callsOf_live hks hcalls err hc
              have := hacc b (by simp only [Data.digests, Data.rowDigests, List.mem_append]; exact .inl (digestAt_mem hb))
              simp [hn] at this
            | ok calls =>
              refine ⟨c, e, ds, calls, rfl, hc, ?_⟩
              unfold runMeasuredLive runMeasuredWith
              simp only [bind, Except.bind, hS', Nat.add_sub_cancel]
              rw [if_neg (by omega)]
              simp only [hr, hx]
              cases stateSlots (recordRow p.state) ds 0 <;>
                simp [hc, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
end


/-- **Every id a run holds is accepted, from the law** (cv 01a14b28-7029): for a lawful `Ctx`
(`Receive.Ctx.Lawful`: its decoder reads every id back), every digest of a method run's extracted
result is one `X.digestOf` accepts. The request's ids need nothing more than the law. -/
theorem runSetup_accepted {rc : Lang.ReceiptCheck} {D : Type} {X : Ctx D} (hX : X.Lawful) {look : Pinned D} {rv : RowView D} {pkg : D}
    {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D} {S : RunSetup}
    {budget used fuel left : Nat} {v : Val} {d : Data}
    (hS : runSetup X.env.bytes X.digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (d, left)) :
    ∀ b ∈ d.digests, (X.digestOf b).isSome = true :=
  runSetup_accepted_of (fun x => by simp [hX.digestOf_bytes x]) hS hr hx

/-- **`callsOf` never refuses a checked run, from the law** (cv 01a14af1-2132, cv 01a14b28-7029): under a
lawful `Ctx`, past extraction the deployed run reads its calls, and what it does next is exactly the
state's slots (refused only for state without bytes), `editsOf`, then `guardEdits`. The law can fail
(`sim_drop_not_lawful`); that the law reaches the decoder the program actually runs with is
`program_run_past_extraction`'s second premise. -/
theorem runMeasured_past_extraction {rc : Lang.ReceiptCheck} {D : Type} {X : Ctx D} (hX : X.Lawful) {look : Pinned D}
    {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D}
    {budget : Nat} {S : RunSetup} {used left : Nat} {v : Val} {d : Data}
    (hS : runSetup X.env.bytes X.digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c e : Data) (ds : List (Label × Data)) (calls : List (Body D)),
      d = .record [("calls", c), ("edits", e), ("state", .record ds)] ∧ callsOf X.digestOf S.calls c = .ok calls ∧
      runMeasured X.env.bytes X.digestOf rc look rv pkg state method args r budget =
        match stateSlots S.row ds 0 with
        | some slots => do
            let es ← editsOf S.rels r.self e
            guardEdits X.env.bytes X.digestOf S rv pkg r es
            pure (slots, calls, es.map (fun x => (x.slot, x.act)), budget - left, S.pkgs)
        | none => .error (.program s!"{S.label}: state bytes") :=
  runMeasured_past_extraction_of (fun x => by simp [hX.digestOf_bytes x]) hS hr hx

/-- **The run a `Ctx`'s program makes reads its calls** (cv 01a14b28-7029): when the `Ctx` is lawful AND
its program is the language over the `Ctx`'s own codec (`hp`: the program decodes with the decoder
the law is about), `X.program.run` past extraction returns the calls `callsOf` read, and what it does
next is exactly the state's slots (refused only for state without bytes), `editsOf`, then
`guardEdits`. The law can fail (`sim_drop_not_lawful`, a refutation, not a run); the second
premise is shown to bite by a run: journey LD5 (PLANT unlawful-codec), a program whose decoder refuses
a member's id inside a lawful Sim `Ctx`, where `callsOf` refuses by name. The deployed `Ctx` meets both
(`Receive.deployed_ctx_lawful`, `deployed_program_own_codec`). -/
theorem program_run_past_extraction_live {rc : Lang.ReceiptCheck} {D : Type} {X : Ctx D} (hX : X.Lawful)
    (hp : X.program = Lang.program X.env.bytes X.digestOf rc) {look : Pinned D} {rv : RowView D}
    {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat}
    {S : RunSetup} {used left : Nat} {v : Val} {d : Data}
    (hS : runSetupLive X.env.bytes X.digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c e : Data) (ds : List (Label × Data)) (calls : List (Body D)),
      d = .record [("calls", c), ("edits", e), ("state", .record ds)] ∧ callsOf X.digestOf S.calls c = .ok calls ∧
      X.program.run look rv pkg state method args r (budget + S.preparation) =
        match stateSlots S.row ds 0 with
        | some slots => do
            let es ← editsOf S.rels r.self e
            guardEdits X.env.bytes X.digestOf S rv pkg r es
            pure (slots, calls, es.map (fun x => (x.slot, x.act)), budget + S.preparation - left)
        | none => .error (.program s!"{S.label}: state bytes") := by
  obtain ⟨c, e, ds, calls, hd, hc, hm⟩ := runMeasuredLive_past_extraction_of (fun x => by simp [hX.digestOf_bytes x]) hS hr hx
  refine ⟨c, e, ds, calls, hd, hc, ?_⟩
  rw [hp]
  show (runMeasuredLive X.env.bytes X.digestOf rc look rv pkg state method args r (budget + S.preparation)).map _ = _
  rw [hm]
  cases stateSlots S.row ds 0 with
  | none => rfl
  | some slots =>
    simp only [bind, Except.bind]
    cases editsOf S.rels r.self e with
    | error _ => rfl
    | ok es => cases hg : guardEdits X.env.bytes X.digestOf S rv pkg r es <;> simp [hg, Except.map, pure, Except.pure]

/- Landed closed statement preserved through the proved deployment bridge. -/
theorem program_run_past_extraction {rc : Lang.ReceiptCheck} {D : Type} {X : Ctx D} (hX : X.Lawful)
    (hp : X.program = Lang.program X.env.bytes X.digestOf rc) {look : Pinned D} {rv : RowView D}
    {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat}
    {S : RunSetup} {used left : Nat} {v : Val} {d : Data}
    (hS : runSetup X.env.bytes X.digestOf rc look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c e : Data) (ds : List (Label × Data)) (calls : List (Body D)),
      d = .record [("calls", c), ("edits", e), ("state", .record ds)] ∧ callsOf X.digestOf S.calls c = .ok calls ∧
      X.program.run look rv pkg state method args r budget =
        match stateSlots S.row ds 0 with
        | some slots => do
            let es ← editsOf S.rels r.self e
            guardEdits X.env.bytes X.digestOf S rv pkg r es
            pure (slots, calls, es.map (fun x => (x.slot, x.act)), budget - left)
        | none => .error (.program s!"{S.label}: state bytes") := by
  obtain ⟨c, e, ds, calls, hd, hc, hm⟩ := runMeasured_past_extraction hX hS hr hx
  refine ⟨c, e, ds, calls, hd, hc, ?_⟩
  rw [hp, program_run_closed hS, hm]
  cases stateSlots S.row ds 0 with
  | none => rfl
  | some slots =>
    simp only [bind, Except.bind]
    cases editsOf S.rels r.self e with
    | error _ => rfl
    | ok es => cases hg : guardEdits X.env.bytes X.digestOf S rv pkg r es <;> simp [hg, Except.map, pure, Except.pure]

/-- The deployed `Ctx`'s program is the language over the deployed codec itself: the second
premise of `program_run_past_extraction` holds there by construction. -/
theorem deployed_program_own_codec {rc : Lang.ReceiptCheck} :
    (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes? rc)).program =
      Lang.program (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes? rc)).env.bytes
        (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes? rc)).digestOf rc := rfl

/-- **The Sim's `Ctx` is lawful**, whatever its program: its decoder reads every toy id back
(`sim_digest_roundtrip`). So `runMeasured_past_extraction` holds at the Sim with no premise. -/
theorem sim_ctx_lawful (prog : Program Kernel.Sim.D) : (Kernel.Sim.ctxWith prog).Lawful :=
  ⟨Teeth.sim_digest_roundtrip⟩

/-- **The law can fail** (KERNEL-12's condition): the Sim's `Ctx` with a decoder that drops the first
byte of what it reads is not lawful; it no longer reads the id 0 back. -/
theorem sim_drop_not_lawful (prog : Program Kernel.Sim.D) :
    ¬ ({ Kernel.Sim.ctxWith prog with
          digestOf := fun b => Kernel.Sim.digestOf (b.extract 1 b.size) } : Ctx Kernel.Sim.D).Lawful :=
  fun h => by
    have h0 : Kernel.Sim.digestOf ((Kernel.Sim.dc.bytes 0).extract 1 (Kernel.Sim.dc.bytes 0).size) = some 0 :=
      h.digestOf_bytes 0
    have hn : Kernel.Sim.digestOf ((Kernel.Sim.dc.bytes 0).extract 1 (Kernel.Sim.dc.bytes 0).size) = none := by
      decide
    rw [hn] at h0
    cases h0

/-- At the Sim, with no premise: every admitted Sim run past extraction reads its calls (the Sim's
decoder reads its ids back, `sim_digest_roundtrip`, the fact `sim_ctx_lawful` is built from), and
what it does next is exactly the state's slots, `editsOf`, then `guardEdits`. -/
theorem runMeasured_past_extraction_sim {look : Pinned Kernel.Sim.D} {rv : RowView Kernel.Sim.D}
    {pkg : Kernel.Sim.D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Req Kernel.Sim.D} {budget : Nat} {S : RunSetup} {used left : Nat}
    {v : Val} {d : Data}
    (hS : runSetup Kernel.Sim.dc.bytes Kernel.Sim.digestOf noReceipts look rv pkg state method args r = .ok S)
    (hr : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left)) :
    ∃ (c e : Data) (ds : List (Label × Data)) (calls : List (Body Kernel.Sim.D)),
      d = .record [("calls", c), ("edits", e), ("state", .record ds)] ∧
      callsOf Kernel.Sim.digestOf S.calls c = .ok calls ∧
      runMeasured Kernel.Sim.dc.bytes Kernel.Sim.digestOf noReceipts look rv pkg state method args r budget =
        match stateSlots S.row ds 0 with
        | some slots => do
            let es ← editsOf S.rels r.self e
            guardEdits Kernel.Sim.dc.bytes Kernel.Sim.digestOf S rv pkg r es
            pure (slots, calls, es.map (fun x => (x.slot, x.act)), budget - left, S.pkgs)
        | none => .error (.program s!"{S.label}: state bytes") :=
  runMeasured_past_extraction_of (fun x => by simp [Teeth.sim_digest_roundtrip]) hS hr hx
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
