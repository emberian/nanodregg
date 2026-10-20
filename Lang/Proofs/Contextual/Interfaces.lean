/-
P11a: de Alfaro–Henzinger, Interface Automata (2001), PDF p10 / printed p118,
Definitions 14–15 and Theorem 4. Specialization to P5's fixed input/output types,
deterministic input transitions, no hidden actions, and closed binary products.
Compatibility here is universal refusal-safety, stronger than optimistic viability.
-/
import Lang.Proofs.Contextual.P5
import Lang.Contextual.Interfaces

namespace Nanodregg.Lang.Contextual.P5.Interfaces

/-- de Alfaro–Henzinger Definition 14(1), PDF p10: externally enabled inputs.
P5 has no hidden transitions, hence epsilon-closure is the singleton state. -/
def InputEnabled {S I O : Type} (m : Machine S I O) (s : S) (i : I) : Prop :=
  ∃ s', m.receive s i = some s'

/-- de Alfaro–Henzinger Definition 14(1), PDF p10: externally enabled outputs. -/
def OutputEnabled {S I O : Type} (m : Machine S I O) (s : S) (o : O) : Prop :=
  ∃ s', (o, s') ∈ m.emit s

/-- de Alfaro–Henzinger Definition 14, PDF p10, including successor matching.
The input successor clause is written from implementation to specification as in
the paper; deterministic receive makes it equivalent to the landed forward clause. -/
structure Definition14 {SI SS I O : Type} (impl : Machine SI I O)
    (spec : Machine SS I O) (R : SI → SS → Prop) : Prop where
  input_inclusion : ∀ si ss, R si ss → ∀ i, InputEnabled spec ss i → InputEnabled impl si i
  output_inclusion : ∀ si ss, R si ss → ∀ o, OutputEnabled impl si o → OutputEnabled spec ss o
  input_successor : ∀ si ss, R si ss → ∀ i, InputEnabled spec ss i →
    ∀ si', impl.receive si i = some si' →
      ∃ ss', spec.receive ss i = some ss' ∧ R si' ss'
  output_successor : ∀ si ss, R si ss → ∀ o si', (o, si') ∈ impl.emit si →
    ∃ ss', (o, ss') ∈ spec.emit ss ∧ R si' ss'

/-- de Alfaro–Henzinger Definition 14, PDF p10: the landed stateful relation is
exactly the paper's enabling inclusions and successor conditions in this fragment. -/
theorem alternatingSimulation_iff_definition14 {SI SS I O : Type}
    {impl : Machine SI I O} {spec : Machine SS I O} {R : SI → SS → Prop} :
    AlternatingSimulation impl spec R ↔ Definition14 impl spec R := by
  constructor
  · intro h
    constructor
    · rintro si ss hr i ⟨ss', hs'⟩
      obtain ⟨si', hi', _⟩ := h.inputs si ss hr i ss' hs'
      exact ⟨si', hi'⟩
    · rintro si ss hr o ⟨si', hi'⟩
      obtain ⟨ss', hs', _⟩ := h.outputs si ss hr o si' hi'
      exact ⟨ss', hs'⟩
    · rintro si ss hr i ⟨ss', hs'⟩ si' hi'
      obtain ⟨si'', hi'', hr'⟩ := h.inputs si ss hr i ss' hs'
      have he : si'' = si' := Option.some.inj (hi''.symm.trans hi')
      subst si''
      exact ⟨ss', hs', hr'⟩
    · exact h.outputs
  · intro h
    constructor
    · intro si ss hr i ss' hs'
      obtain ⟨si', hi'⟩ := h.input_inclusion si ss hr i ⟨ss', hs'⟩
      obtain ⟨ss'', hs'', hr'⟩ := h.input_successor si ss hr i ⟨ss', hs'⟩ si' hi'
      have he : ss'' = ss' := Option.some.inj (hs''.symm.trans hs')
      subst ss''
      exact ⟨si', hi', hr'⟩
    · exact h.output_successor

/-- de Alfaro–Henzinger Definitions 14–15, PDF p10: pointed refinement, with the
global alphabet variance automatic because both machines use the same I/O types. -/
theorem refines_iff_definition14 {SI SS I O : Type} {impl : Machine SI I O}
    {spec : Machine SS I O} {si : SI} {ss : SS} :
    Refines impl si spec ss ↔ ∃ R, R si ss ∧ Definition14 impl spec R := by
  constructor
  · rintro ⟨R, hr, hs⟩
    exact ⟨R, hr, alternatingSimulation_iff_definition14.mp hs⟩
  · rintro ⟨R, hr, hs⟩
    exact ⟨R, hr, alternatingSimulation_iff_definition14.mpr hs⟩

/-- de Alfaro–Henzinger Theorem 4, PDF p10: our closed-peer compatibility requires
all finite mixed sessions safe. It implies viability, but does not assert progress. -/
def Compatible {S P I O : Type} (m : Machine S I O) (s : S)
    (peer : Machine P O I) (p : P) : Prop :=
  ∀ n, SafeFor m peer n s p

/-- de Alfaro–Henzinger product synchronization (PDF pp5–6): both alphabets are
shared, hence each move is a handshake. We retain its label for trace simulation;
this is a product transition relation, not a second interface-automaton datatype. -/
inductive ProductMoves {S P I O : Type} (m : Machine S I O) (peer : Machine P O I) :
    (S × P) → Action I O → (S × P) → Prop where
  | input {s s' p p' i} : (i, p') ∈ peer.emit p → m.receive s i = some s' →
    ProductMoves m peer (s, p) (.input i) (s', p')
  | output {s s' p p' o} : (o, s') ∈ m.emit s → peer.receive p o = some p' →
    ProductMoves m peer (s, p) (.output o) (s', p')

/-- de Alfaro–Henzinger Theorem 4, PDF p10: synchronized product transitions
simulate under replacement, including the peer's actual successor, not just labels. -/
theorem product_matching {SI SS P I O : Type} {impl : Machine SI I O}
    {spec : Machine SS I O} {peer : Machine P O I} {R : SI → SS → Prop}
    (hsim : AlternatingSimulation impl spec R) {si : SI} {ss : SS} {p : P}
    (hr : R si ss) (hc : Compatible spec ss peer p)
    {a : Action I O} {si' : SI} {p' : P}
    (hm : ProductMoves impl peer (si, p) a (si', p')) :
    ∃ ss', ProductMoves spec peer (ss, p) a (ss', p') ∧
      R si' ss' ∧ Compatible spec ss' peer p' := by
  cases hm with
  | input hp hi =>
    obtain ⟨ss', hs', _⟩ := (hc 1).1 _ _ hp
    obtain ⟨si'', hi'', hr'⟩ := hsim.inputs si ss hr _ ss' hs'
    have he : si'' = si' := Option.some.inj (hi''.symm.trans hi)
    subst si''
    refine ⟨ss', .input hp hs', hr', ?_⟩
    intro n
    obtain ⟨s, hs, hn⟩ := (hc (n + 1)).1 _ _ hp
    have he : s = ss' := Option.some.inj (hs.symm.trans hs')
    subst s
    exact hn
  | output hi hp =>
    obtain ⟨ss', hs', hr'⟩ := hsim.outputs si ss hr _ si' hi
    refine ⟨ss', .output hs' hp, hr', ?_⟩
    intro n
    obtain ⟨q, hq, hn⟩ := (hc (n + 1)).2 _ _ hs'
    have he : q = p' := Option.some.inj (hq.symm.trans hp)
    subst q
    exact hn

/-- de Alfaro–Henzinger Theorem 4, PDF p10, closed same-alphabet specialization:
a compatible peer survives replacement AND every implementation product step
has a specification product step under a successor-closed relation.
The paper's no-new-peer-input side condition is enforced by the common alphabets. -/
theorem substitutivity {SI SS P I O : Type} {impl : Machine SI I O}
    {spec : Machine SS I O} {peer : Machine P O I} {si : SI} {ss : SS} {p : P}
    (href : Refines impl si spec ss) (hc : Compatible spec ss peer p) :
    Compatible impl si peer p ∧
      ∃ T : (SI × P) → (SS × P) → Prop, T (si, p) (ss, p) ∧
        ∀ u v, T u v → ∀ a u', ProductMoves impl peer u a u' →
          ∃ v', ProductMoves spec peer v a v' ∧ T u' v' := by
  obtain ⟨R, hr, hs⟩ := href
  refine ⟨fun n => simulation_preserves_safety hs peer n hr (hc n),
    (fun u v => u.2 = v.2 ∧ R u.1 v.1 ∧ Compatible spec v.1 peer v.2),
    ⟨rfl, hr, hc⟩, ?_⟩
  rintro ⟨i, q⟩ ⟨s, r⟩ ⟨he, hrs, hcs⟩ a ⟨i', q'⟩ hm
  dsimp at he hrs hcs
  subst r
  obtain ⟨s', hm', hr', hc'⟩ := product_matching hs hrs hcs hm
  exact ⟨(s', q'), hm', rfl, hr', hc'⟩

end Nanodregg.Lang.Contextual.P5.Interfaces

namespace Nanodregg.Lang.Contextual.P5.Interfaces

/-- de Alfaro–Henzinger Theorem 4, PDF p10: an inhabited infinite family of
finite safe horizons, including both Boolean replies and repeated negotiations. -/
theorem seven_peer_compatible (s : Bool) :
    Compatible (priceReceiver 10 [true, false]) s sevenPeer s := by
  intro n
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    cases s with
    | false =>
      constructor
      · intro i p' hp
        simp only [sevenPeer, Bool.false_eq_true, if_false, List.mem_cons,
          List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨true, by decide, ih true⟩
      · intro o s' hs
        simp [priceReceiver] at hs
    | true =>
      constructor
      · intro i p' hp
        simp [sevenPeer] at hp
      · intro o s' hs
        simp only [priceReceiver, if_true, List.map_cons, List.map_nil, List.mem_cons,
          List.mem_nil_iff, or_false, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨false, by decide, ih false⟩
        · exact ⟨false, by decide, ih false⟩

/-- de Alfaro–Henzinger Theorem 4, PDF p10: the concrete seven-peer remains
compatible after increasing accepted prices and removing the false reply. -/
theorem seven_peer_survives :
    Compatible (priceReceiver 20 [true]) false sevenPeer false :=
  (substitutivity
    (price_refines (small := 10) (large := 20) (by decide)
      (outs := [true, false]) (outs' := [true]) (by simp) false)
    (seven_peer_compatible false)).1

/-- de Alfaro–Henzinger Definition 14(2), PDF p10: current label inclusion alone
is insufficient. These receivers disagree at the successor, after two inputs. -/
theorem enabling_alone_insufficient :
    (∀ i, InputEnabled (twiceReceiver true) false i →
      InputEnabled (twiceReceiver false) false i) ∧
    (∀ o, OutputEnabled (twiceReceiver false) false o →
      OutputEnabled (twiceReceiver true) false o) ∧
    ¬ Refines (twiceReceiver false) false (twiceReceiver true) false := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    exact ⟨true, by simp [twiceReceiver]⟩
  · rintro o ⟨s, hs⟩
    simp [twiceReceiver] at hs
  · rintro ⟨R, hr, hs⟩
    obtain ⟨s, he, _⟩ := simulation_receives hs [(), ()] hr (ss' := true) (by decide)
    simp [receiveAll, twiceReceiver] at he

end Nanodregg.Lang.Contextual.P5.Interfaces
