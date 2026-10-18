/-
# Kernel.Proofs.Fold — what a log means, and why a follower can trust a head

`World.fold` is the follower and the reopening Host. The headline theorem, `chain_binds`: two
logs of the same length that reach the same chain from the same genesis are the same log, or two
of the inputs the two chains compare collide (`CollidesAmong E.hash (chainPres …)`; its tooth
`chain_binds_sep`) — so a follower that checks one signed `(steps, chain)` (KERNEL-47: a recorded
refusal advances the steps and the chain, not the height) knows every turn before it.
-/
import Kernel.Proofs.Refuse
import Kernel.Proofs.Bytes
import Kernel.Proofs.Lawful

namespace Nanodregg.Kernel

section Chain
variable {D : Type}

/-! ### Escapes name their inputs

A digest equality the kernel compares can fail to bind only where the hash maps two DIFFERENT
inputs to one digest, and the inputs in question are the theorem's own: the (domain, bytes) inputs
of the digests it compares. `CollidesAmong hash S` says exactly that, for a list `S` each theorem
builds from its own objects (`linkPre`, `chainPres`, `foldPres`, ...). A collision among SOME two
inputs holds of every hash into a finite `D` by pigeonhole, so `E.Lawful` proves it and it would make
every disjunct it appears in vacuous. `Separates hash S` (the hash tells the inputs of `S` apart) is
the tooth: under it each theorem's conclusion is its binding fact alone (`Separates.elim`). -/

/-- Two different inputs, both in `S`, with one digest. -/
def CollidesAmong (hash : String → ByteArray → D) (S : List (String × ByteArray)) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ hash p.1 p.2 = hash q.1 q.2

theorem CollidesAmong.mono {hash : String → ByteArray → D} {S S' : List (String × ByteArray)}
    (hsub : ∀ x ∈ S, x ∈ S') : CollidesAmong hash S → CollidesAmong hash S'
  | ⟨p, hp, q, hq, hne, h⟩ => ⟨p, hsub p hp, q, hsub q hq, hne, h⟩

/-- Two different inputs with one digest collide among the pair. -/
theorem CollidesAmong.pair {hash : String → ByteArray → D} {p q : String × ByteArray} (hne : p ≠ q)
    (h : hash p.1 p.2 = hash q.1 q.2) : CollidesAmong hash [p, q] :=
  ⟨p, by simp, q, by simp, hne, h⟩

/-- The hash tells the inputs of `S` apart. -/
def Separates (hash : String → ByteArray → D) (S : List (String × ByteArray)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, hash p.1 p.2 = hash q.1 q.2 → p = q

theorem Separates.not_collides {hash : String → ByteArray → D} {S : List (String × ByteArray)}
    (hs : Separates hash S) : ¬ CollidesAmong hash S
  | ⟨p, hp, q, hq, hne, h⟩ => hne (hs p hp q hq h)

/-- **The tooth's form.** Under `Separates hash S`, a conclusion `P ∨ CollidesAmong hash S` is `P`. -/
theorem Separates.elim {hash : String → ByteArray → D} {S : List (String × ByteArray)} {P : Prop}
    (hs : Separates hash S) (h : P ∨ CollidesAmong hash S) : P :=
  h.resolve_right hs.not_collides

theorem Separates.mono {hash : String → ByteArray → D} {S S' : List (String × ByteArray)}
    (hsub : ∀ x ∈ S, x ∈ S') (hs : Separates hash S') : Separates hash S :=
  fun p hp q hq h => hs p (hsub p hp) q (hsub q hq) h

/-- An injective hash separates every list: `Separates` is no contradiction. -/
theorem separates_of_injective {hash : String → ByteArray → D}
    (hinj : ∀ d a e b, hash d a = hash e b → d = e ∧ a = b) (S : List (String × ByteArray)) :
    Separates hash S :=
  fun _ _ _ _ h => Prod.ext (hinj _ _ _ _ h).1 (hinj _ _ _ _ h).2

/-- `Env.Lawful` says nothing of the hash: an `Env` with its hash swapped stays lawful. -/
theorem Env.Lawful.withHash [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) (f : String → ByteArray → D) :
    ({ E with hash := f } : Env D).Lawful n :=
  ⟨hE.size, hE.n_le, hE.bytes_inj, hE.turnBytes_injOn, hE.cellBytes_injOn⟩

/-- **The floor of `Separates` under a lawful `Env`.** Over a `D` with two distinct digests, every
lawful `Env` has a lawful sibling (its hash swapped for a toy one) that separates the concrete
two-input list `S₀` (satisfiable), and one that does not (refutable): the lawful premises neither
force a tooth's `Separates` premise nor exclude it. At the deployed width: `separates_floor_32`. -/
theorem separates_lawful_floor [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {a b : D} (hab : a ≠ b) :
    (∃ E' : Env D, E'.Lawful n ∧ Separates E'.hash [("a", ByteArray.empty), ("b", ByteArray.empty)]) ∧
      ∃ E' : Env D, E'.Lawful n ∧ ¬ Separates E'.hash [("a", ByteArray.empty), ("b", ByteArray.empty)] := by
  refine ⟨⟨{ E with hash := fun dom _ => if dom = "a" then a else b }, hE.withHash _, ?_⟩,
    ⟨{ E with hash := fun _ _ => a }, hE.withHash _, ?_⟩⟩
  · intro p hp q hq h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp_all
  · intro hs
    have := hs ("a", ByteArray.empty) (by simp) ("b", ByteArray.empty) (by simp) rfl
    simp at this

theorem stepLink_eq (E : Env D) (c : D) (s : Step D) (rs : D) :
    stepLink E c s rs = headLink E c s.tag (stepDigest E s) rs := by
  cases s <;> rfl

theorem chainOf_concat {E : Env D} :
    ∀ {c : D} {l : List (Step D × D)} {t : Step D} {r : D},
      chainOf E c (l ++ [(t, r)]) = stepLink E (chainOf E c l) t r
  | c, [], t, r => rfl
  | c, (x, rx) :: rest, t, r => by
      show chainOf E (stepLink E c x rx) (rest ++ [(t, r)]) = _
      rw [chainOf_concat]; rfl

theorem chainPres_concat {E : Env D} :
    ∀ {c : D} {l : List (Step D × D)} {t : Step D} {r : D},
      chainPres E c (l ++ [(t, r)]) = chainPres E c l ++ stepPres E (chainOf E c l) t r
  | c, [], t, r => by simp [chainPres, chainOf]
  | c, (x, rx) :: rest, t, r => by
      show stepPres E c x rx ++ chainPres E (stepLink E c x rx) (rest ++ [(t, r)]) = _
      rw [chainPres_concat]; simp [chainPres, chainOf]

theorem nat64_size (k : Nat) : (Nanodregg.Codec.Stream.nat64.bytes k).size = 8 := by
  rw [Nanodregg.Codec.Stream.nat64_bytes, Nanodregg.Codec.Stream.u64_bytes]; rfl

theorem counterLimit_eq : Bounds.counterLimit = 2 ^ 64 := by decide

/-- One head link determines its predecessor, its kind byte, its step digest and its roots digest,
or the two links' inputs collide (in `domChain`). -/
theorem headLink_inj [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n)
    {c₁ c₂ d₁ d₂ r₁ r₂ : D} {g₁ g₂ : UInt8}
    (h : headLink E c₁ g₁ d₁ r₁ = headLink E c₂ g₂ d₂ r₂) :
    (c₁ = c₂ ∧ g₁ = g₂ ∧ d₁ = d₂ ∧ r₁ = r₂) ∨
      CollidesAmong E.hash [linkPre E c₁ g₁ d₁ r₁, linkPre E c₂ g₂ d₂ r₂] := by
  unfold headLink at h
  by_cases hin : (⟨#[g₁]⟩ : ByteArray) ++ E.bytes c₁ ++ E.bytes d₁ ++ E.bytes r₁ =
      ⟨#[g₂]⟩ ++ E.bytes c₂ ++ E.bytes d₂ ++ E.bytes r₂
  · obtain ⟨hgcd, hr⟩ := bytes_append_inj hin (by simp [hE.size])
    obtain ⟨hgc, hd⟩ := bytes_append_inj hgcd (by simp [hE.size])
    obtain ⟨hg, hc⟩ := bytes_append_inj hgc rfl
    have hg' : g₁ = g₂ := by
      have := congrArg (fun z : ByteArray => z.data.toList) hg
      simpa using this
    exact .inl ⟨hE.bytes_inj hc, hg', hE.bytes_inj hd, hE.bytes_inj hr⟩
  · exact .inr (.pair (fun he => hin (congrArg Prod.snd he)) h)

/-- A recorded refusal's digest determines it, within `Bounds`, or the two inputs collide (in
`domRefused`). -/
theorem refusedDigest_inj [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {r₁ r₂ : Refused D}
    (hb₁ : checkRefusedBounds r₁ = .ok ()) (hb₂ : checkRefusedBounds r₂ = .ok ())
    (h : refusedDigest E r₁ = refusedDigest E r₂) :
    r₁ = r₂ ∨ CollidesAmong E.hash [refusedPre E r₁, refusedPre E r₂] := by
  have bnd : ∀ {r : Refused D}, checkRefusedBounds r = .ok () →
      r.notBefore < 2 ^ 64 ∧ r.validUntil < 2 ^ 64 ∧ r.code < 2 ^ 64 := by
    intro r hb
    unfold checkRefusedBounds at hb
    simp only [except_bind_ok] at hb
    obtain ⟨⟨⟩, -, ⟨⟩, hc, -⟩ := hb
    have := req_ok.mp hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, counterLimit_eq] at this
    omega
  obtain ⟨a₁, b₁, c₁⟩ := bnd hb₁
  obtain ⟨a₂, b₂, c₂⟩ := bnd hb₂
  unfold refusedDigest at h
  by_cases hin : refusedBytes E r₁ = refusedBytes E r₂
  · unfold refusedBytes at hin
    obtain ⟨h5, hev⟩ := bytes_append_inj hin (by simp [hE.size, nat64_size])
    obtain ⟨h4, hco⟩ := bytes_append_inj h5 (by simp [hE.size, nat64_size])
    obtain ⟨h3, hvu⟩ := bytes_append_inj h4 (by simp [hE.size, nat64_size])
    obtain ⟨h2, hnb⟩ := bytes_append_inj h3 (by simp [hE.size])
    obtain ⟨h1, hm⟩ := bytes_append_inj h2 (by simp [hE.size])
    cases r₁; cases r₂
    simp only [Refused.mk.injEq]
    exact .inl ⟨hE.bytes_inj h1, hE.bytes_inj hm, Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective a₁ a₂ hnb,
      Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective b₁ b₂ hvu,
      Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective c₁ c₂ hco, hev⟩
  · exact .inr (.pair (fun he => hin (congrArg Prod.snd he)) h)

/-- One chain step between bounded steps determines its predecessor, its step and the roots digest
after it, or the two steps' inputs collide (`stepPres`: the links', the step digests'): a turn link
is never a refusal link (the kind byte), and each kind's digest determines its step. -/
theorem stepLink_inj [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n)
    {c₁ c₂ : D} {r₁ r₂ : D} {s₁ s₂ : Step D} (hb₁ : s₁.Bounded) (hb₂ : s₂.Bounded)
    (h : stepLink E c₁ s₁ r₁ = stepLink E c₂ s₂ r₂) :
    (c₁ = c₂ ∧ s₁ = s₂ ∧ r₁ = r₂) ∨ CollidesAmong E.hash (stepPres E c₁ s₁ r₁ ++ stepPres E c₂ s₂ r₂) := by
  have hsub : ∀ {a b : String × ByteArray}, a = stepLinkPre E c₁ s₁ r₁ ∨ a = stepPre E s₁ →
      b = stepLinkPre E c₂ s₂ r₂ ∨ b = stepPre E s₂ →
      ∀ x ∈ [a, b], x ∈ stepPres E c₁ s₁ r₁ ++ stepPres E c₂ s₂ r₂ := by
    intro a b ha hb x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · rcases ha with rfl | rfl <;> simp [stepPres]
    · rcases hb with rfl | rfl <;> simp [stepPres]
  rw [stepLink_eq, stepLink_eq] at h
  rcases headLink_inj hE h with ⟨hc, hg, hd, hr⟩ | hcol
  · cases s₁ <;> cases s₂ <;> simp only [Step.tag, stepDigest] at hg hd
    · rename_i t₁ t₂
      unfold turnDigest at hd
      by_cases hti : E.turnBytes t₁ = E.turnBytes t₂
      · exact .inl ⟨hc, by rw [hE.turnBytes_injOn hb₁ hb₂ hti], hr⟩
      · exact .inr (CollidesAmong.mono (hsub (.inr rfl) (.inr rfl))
          (.pair (fun he => hti (congrArg Prod.snd he)) hd))
    · simp at hg
    · simp at hg
    · rename_i q₁ q₂
      rcases refusedDigest_inj hE hb₁ hb₂ hd with rfl | hcol
      · exact .inl ⟨hc, rfl, hr⟩
      · exact .inr (CollidesAmong.mono (hsub (.inr rfl) (.inr rfl)) hcol)
  · exact .inr (CollidesAmong.mono (hsub (.inl rfl) (.inl rfl)) hcol)

/-- **Follower soundness.** Two logs of one length that reach one chain from one start are one
log with one roots digest after every step, or two of the inputs the two chains compare collide
(`chainPres` of both logs: each step's link and step digest), provided every step of both logs is
bounded (an admitted or recorded step always is: `fold_bounded`). With `fold_chain` and
`fold_steps`: a follower holding a trusted `(steps, chain)` holds the only log that produces it. -/
theorem chain_binds [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {c : D} :
    ∀ (k : Nat) (l₁ l₂ : List (Step D × D)), l₁.length = k → l₂.length = k →
      (∀ p ∈ l₁, p.1.Bounded) → (∀ p ∈ l₂, p.1.Bounded) →
      chainOf E c l₁ = chainOf E c l₂ → l₁ = l₂ ∨ CollidesAmong E.hash (chainPres E c l₁ ++ chainPres E c l₂)
  | 0, l₁, l₂, h₁, h₂, _, _, _ => by
      rw [List.length_eq_zero_iff] at h₁ h₂; subst h₁; subst h₂; exact Or.inl rfl
  | k + 1, l₁, l₂, h₁, h₂, hl₁, hl₂, h => by
      rcases List.eq_nil_or_concat l₁ with rfl | ⟨a₁, ⟨t₁, r₁⟩, rfl⟩
      · simp at h₁
      rcases List.eq_nil_or_concat l₂ with rfl | ⟨a₂, ⟨t₂, r₂⟩, rfl⟩
      · simp at h₂
      simp only [List.concat_eq_append] at h h₁ h₂ hl₁ hl₂ ⊢
      rw [chainOf_concat, chainOf_concat] at h
      rw [chainPres_concat, chainPres_concat]
      rcases stepLink_inj hE (hl₁ _ (List.mem_append_right _ (List.mem_singleton_self _)))
          (hl₂ _ (List.mem_append_right _ (List.mem_singleton_self _))) h with ⟨hc, rfl, rfl⟩ | hcol
      · simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h₁ h₂
        rcases chain_binds hE k a₁ a₂ h₁ h₂ (fun p hp => hl₁ p (List.mem_append_left _ hp))
            (fun p hp => hl₂ p (List.mem_append_left _ hp)) hc with rfl | hcol
        · exact Or.inl rfl
        · refine Or.inr (CollidesAmong.mono (fun x hx => ?_) hcol)
          simp only [List.mem_append] at hx ⊢
          rcases hx with hx | hx <;> simp [hx]
      · refine Or.inr (CollidesAmong.mono (fun x hx => ?_) hcol)
        simp only [List.mem_append] at hx ⊢
        rcases hx with hx | hx <;> simp [hx]

/-- TOOTH (`headLink_inj`): under a hash that separates the two links' inputs, one link is one
(predecessor, kind, digest, roots digest). -/
theorem headLink_inj_sep [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n)
    {c₁ c₂ d₁ d₂ r₁ r₂ : D} {g₁ g₂ : UInt8}
    (hs : Separates E.hash [linkPre E c₁ g₁ d₁ r₁, linkPre E c₂ g₂ d₂ r₂])
    (h : headLink E c₁ g₁ d₁ r₁ = headLink E c₂ g₂ d₂ r₂) : c₁ = c₂ ∧ g₁ = g₂ ∧ d₁ = d₂ ∧ r₁ = r₂ :=
  hs.elim (headLink_inj hE h)

/-- TOOTH (`refusedDigest_inj`). -/
theorem refusedDigest_inj_sep [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {r₁ r₂ : Refused D}
    (hb₁ : checkRefusedBounds r₁ = .ok ()) (hb₂ : checkRefusedBounds r₂ = .ok ())
    (hs : Separates E.hash [refusedPre E r₁, refusedPre E r₂])
    (h : refusedDigest E r₁ = refusedDigest E r₂) : r₁ = r₂ :=
  hs.elim (refusedDigest_inj hE hb₁ hb₂ h)

/-- TOOTH (`stepLink_inj`): under a hash that separates the two steps' inputs, one link is one step. -/
theorem stepLink_inj_sep [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n)
    {c₁ c₂ : D} {r₁ r₂ : D} {s₁ s₂ : Step D} (hb₁ : s₁.Bounded) (hb₂ : s₂.Bounded)
    (hs : Separates E.hash (stepPres E c₁ s₁ r₁ ++ stepPres E c₂ s₂ r₂))
    (h : stepLink E c₁ s₁ r₁ = stepLink E c₂ s₂ r₂) : c₁ = c₂ ∧ s₁ = s₂ ∧ r₁ = r₂ :=
  hs.elim (stepLink_inj hE hb₁ hb₂ h)

/-- TOOTH (`chain_binds`): under a hash that separates the inputs both chains compare, one chain is
one log. -/
theorem chain_binds_sep [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {c : D}
    {l₁ l₂ : List (Step D × D)} (hl : l₁.length = l₂.length)
    (hb₁ : ∀ p ∈ l₁, p.1.Bounded) (hb₂ : ∀ p ∈ l₂, p.1.Bounded)
    (hs : Separates E.hash (chainPres E c l₁ ++ chainPres E c l₂))
    (h : chainOf E c l₁ = chainOf E c l₂) : l₁ = l₂ :=
  hs.elim (chain_binds hE l₁.length l₁ l₂ rfl hl.symm hb₁ hb₂ h)

end Chain

variable {D : Type} [Ord D] [DecidableEq D]

theorem fold_cons_ok {E : Env D} {w w'' : World D} {t : Step D} {rest : List (Step D)} :
    World.fold E w (t :: rest) = .ok w'' ↔
      ∃ w', World.step E w t = .ok w' ∧ World.fold E w' rest = .ok w'' := by
  conv => lhs; unfold World.fold
  cases ha : World.step E w t with
  | error r => simp
  | ok w' =>
      cases hf : World.fold E w' rest with
      | error e => obtain ⟨i, r⟩ := e; simp [hf]
      | ok v => simp [hf]

/-- A log's fold is the fold of its pieces: restart from any admitted prefix is sound. -/
theorem fold_append {E : Env D} :
    ∀ {w w'' : World D} {l₁ l₂ : List (Step D)},
      World.fold E w (l₁ ++ l₂) = .ok w'' ↔
        ∃ w', World.fold E w l₁ = .ok w' ∧ World.fold E w' l₂ = .ok w''
  | w, w'', [], l₂ => by simp [World.fold]
  | w, w'', t :: rest, l₂ => by
      rw [List.cons_append, fold_cons_ok]
      constructor
      · rintro ⟨w₁, h₁, h₂⟩
        obtain ⟨w', h₃, h₄⟩ := (fold_append (l₁ := rest)).mp h₂
        exact ⟨w', fold_cons_ok.mpr ⟨w₁, h₁, h₃⟩, h₄⟩
      · rintro ⟨w', h₁, h₂⟩
        obtain ⟨w₁, h₃, h₄⟩ := fold_cons_ok.mp h₁
        exact ⟨w₁, h₃, (fold_append (l₁ := rest)).mpr ⟨w', h₄, h₂⟩⟩

/-- A one-turn log is the turn's admission. -/
theorem fold_turn {E : Env D} {w w' : World D} {t : Turn D} :
    World.fold E w [.turn t] = .ok w' ↔ World.admit E w t = .ok w' := by
  rw [fold_cons_ok]
  constructor
  · rintro ⟨w₁, h₁, h₂⟩; simp [World.fold] at h₂; subst h₂; exact h₁
  · intro h; exact ⟨w', h, rfl⟩

omit [Ord D] [DecidableEq D] in
theorem turns_append (l₁ l₂ : List (Step D)) : Step.turns (l₁ ++ l₂) = Step.turns l₁ ++ Step.turns l₂ := by
  induction l₁ with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [Step.turns, ih]

omit [Ord D] [DecidableEq D] in
theorem turns_map (l : List (Turn D)) : Step.turns (l.map .turn) = l := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [Step.turns, ih]

omit [Ord D] [DecidableEq D] in
theorem mem_turns {t : Turn D} : ∀ {l : List (Step D)}, t ∈ Step.turns l ↔ Step.turn t ∈ l
  | [] => by simp [Step.turns]
  | .turn u :: rest => by simp [Step.turns, mem_turns]
  | .refusal _ :: rest => by simp [Step.turns, mem_turns]

/-- A log's height: one per Turn; a recorded refusal advances none (KERNEL-44: windows are in
heights, so no refusal shortens anyone's window). -/
theorem fold_height {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold E w l = .ok w' →
      w'.height = w.height + (Step.turns l).length
  | w, w', [], h => by simp [World.fold] at h; subst h; simp [Step.turns]
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_height h₂, step_height h₁]
      cases t <;> simp [Step.turns, Step.dheight] <;> omega

/-- A log's steps: one per step, Turn or refusal (KERNEL-47 amendment 1). -/
theorem fold_steps {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold E w l = .ok w' → w'.steps = w.steps + l.length
  | w, w', [], h => by simp [World.fold] at h; subst h; simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_steps h₂, step_steps h₁]; simp; omega

/-- **Height and steps differ by the refusals.** Over a log, the steps advance by its Turns plus its
recorded refusals and the height by its Turns alone (ROOT's condition on KERNEL-47 (1)). -/
theorem fold_steps_height {E : Env D} {w w' : World D} {l : List (Step D)} (h : World.fold E w l = .ok w') :
    w'.steps + w.height = w.steps + w'.height + (Step.refusals l).length := by
  have hs := fold_steps h
  have hh := fold_height h
  have : l.length = (Step.turns l).length + (Step.refusals l).length := by
    clear hs hh h
    induction l with
    | nil => rfl
    | cons s rest ih => cases s <;> simp [Step.turns, Step.refusals, ih] <;> omega
  omega

/-- `height ≤ steps` is kept by every fold (genesis starts both at 0, a carry sets steps to the height):
CODEC's decode refuses a base without it (`kernel/steps`). -/
theorem fold_height_le_steps {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.height ≤ w.steps)
    (h : World.fold E w l = .ok w') : w'.height ≤ w'.steps := by
  have := fold_steps_height h; omega

/-- The chain a fold stamps: the log's steps, each with the roots digest its step left; the inputs
that chain compares are the fold's (`foldPres`). -/
theorem fold_chain {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold E w l = .ok w' →
      ∃ rs : List D, rs.length = l.length ∧ w'.chain = chainOf E w.chain (l.zip rs) ∧
        (l ≠ [] → rs.getLast? = some (w'.roots E)) ∧ chainPres E w.chain (l.zip rs) = foldPres E w l
  | w, w', [], h => by
      simp [World.fold] at h; subst h; exact ⟨[], rfl, rfl, fun h => absurd rfl h, rfl⟩
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      obtain ⟨rs, hl, hc, hr, hp⟩ := fold_chain h₂
      refine ⟨w₁.roots E :: rs, by simp [hl], ?_, fun _ => ?_, ?_⟩
      · rw [hc, step_chain h₁]; rfl
      · cases rest with
        | nil =>
            simp at hl; subst hl
            simp [World.fold] at h₂; subst h₂; rfl
        | cons u us =>
            simp [List.getLast?_cons, hr (by simp)]
      · show stepPres E w.chain t (w₁.roots E) ++ chainPres E (stepLink E w.chain t (w₁.roots E)) (rest.zip rs) = _
        rw [← step_chain h₁, hp]
        simp only [foldPres, h₁]

/-- **Charge exactness over a log.** Each turn of an admitted log paid exactly its weight (where
the budget went is `Kernel.Proofs.Weight.fold_conserves`). -/
theorem fold_charge {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold E w l = .ok w' →
      ∀ t ∈ Step.turns l, t.charge = t.weight
  | w, w', [], _ => by simp [Step.turns]
  | w, w', s :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      intro x hx
      cases s with
      | turn t =>
          simp only [Step.turns, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact (admit_charge h₁).1
          · exact fold_charge h₂ x hx
      | refusal r => exact fold_charge h₂ x hx

/-- An admitted turn is bounded. -/
theorem admit_bounded {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : checkBounds t = .ok () := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  exact hc.bounds

/-- Every step of an admitted log is bounded: the premise `chain_binds` needs, met by every fold. -/
theorem fold_bounded {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold E w l = .ok w' → ∀ s ∈ l, s.Bounded
  | w, w', [], _ => by simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact step_bounded h₁
      · exact fold_bounded h₂ x hx

/-- The follower's theorem in its usable form: same start, same `(steps, chain)` after folding, same
log, or two of the inputs the two folds' chains compare collide (`foldPres` of both logs). KERNEL-47
amendment 1: the premise is equal STEPS, not equal height; a refusal advances the chain and the steps
but not the height. -/
theorem fold_head_binds {E : Env D} {n : Nat} (hE : E.Lawful n)
    {g w₁ w₂ : World D} {l₁ l₂ : List (Step D)}
    (h₁ : World.fold E g l₁ = .ok w₁) (h₂ : World.fold E g l₂ = .ok w₂)
    (hs : w₁.steps = w₂.steps) (hc : w₁.chain = w₂.chain) :
    l₁ = l₂ ∨ CollidesAmong E.hash (foldPres E g l₁ ++ foldPres E g l₂) := by
  have hl : l₁.length = l₂.length := by
    have := fold_steps h₁; have := fold_steps h₂; omega
  obtain ⟨rs₁, hr₁, hc₁, _, hp₁⟩ := fold_chain h₁
  obtain ⟨rs₂, hr₂, hc₂, _, hp₂⟩ := fold_chain h₂
  rw [hc₁, hc₂] at hc
  rw [← hp₁, ← hp₂]
  rcases chain_binds hE l₁.length (l₁.zip rs₁) (l₂.zip rs₂) (by simp [hr₁])
      (by simp [hr₂, hl]) (fun p hp => fold_bounded h₁ p.1 (List.of_mem_zip hp).1)
      (fun p hp => fold_bounded h₂ p.1 (List.of_mem_zip hp).1) hc with he | hcol
  · left
    have := congrArg (List.map Prod.fst) he
    rwa [List.map_fst_zip (by omega), List.map_fst_zip (by omega)] at this
  · exact .inr hcol

/-- `World.fold` is a function of its log. -/
theorem fold_det {E : Env D} {g w₁ w₂ : World D} {l : List (Step D)}
    (h₁ : World.fold E g l = .ok w₁) (h₂ : World.fold E g l = .ok w₂) : w₁ = w₂ := by
  rw [h₁] at h₂; exact Except.ok.inj h₂

/-- **The fold reaches the host's World.** A follower that folds a log from the host's genesis and
reaches the host's `(steps, chain)` holds the host's World — every cell, nullifier, journal entry,
recorded refusal, the budget and the root — or two of the inputs the two folds' chains compare
collide (`foldPres` of the follower's log and of the host's). -/
theorem fold_reaches_host {E : Env D} {n : Nat} (hE : E.Lawful n)
    {g host follower : World D} {lh lf : List (Step D)}
    (hh : World.fold E g lh = .ok host) (hf : World.fold E g lf = .ok follower)
    (hst : follower.steps = host.steps) (hc : follower.chain = host.chain) :
    follower = host ∨ CollidesAmong E.hash (foldPres E g lf ++ foldPres E g lh) := by
  rcases fold_head_binds hE hf hh hst hc with rfl | hcol
  · exact .inl (fold_det hf hh)
  · exact .inr hcol

/-- TOOTH (`fold_head_binds`): under a hash that separates the inputs both folds' chains compare,
one `(steps, chain)` is one log. -/
theorem fold_head_binds_sep {E : Env D} {n : Nat} (hE : E.Lawful n)
    {g w₁ w₂ : World D} {l₁ l₂ : List (Step D)}
    (h₁ : World.fold E g l₁ = .ok w₁) (h₂ : World.fold E g l₂ = .ok w₂)
    (hs : w₁.steps = w₂.steps) (hc : w₁.chain = w₂.chain)
    (hsep : Separates E.hash (foldPres E g l₁ ++ foldPres E g l₂)) : l₁ = l₂ :=
  hsep.elim (fold_head_binds hE h₁ h₂ hs hc)

/-- TOOTH (`fold_reaches_host`): under a hash that separates the inputs both folds' chains compare,
the follower at the host's head holds the host's World. -/
theorem fold_reaches_host_sep {E : Env D} {n : Nat} (hE : E.Lawful n)
    {g host follower : World D} {lh lf : List (Step D)}
    (hh : World.fold E g lh = .ok host) (hf : World.fold E g lf = .ok follower)
    (hst : follower.steps = host.steps) (hc : follower.chain = host.chain)
    (hsep : Separates E.hash (foldPres E g lf ++ foldPres E g lh)) : follower = host :=
  hsep.elim (fold_reaches_host hE hh hf hst hc)

/-- `World.fold` is the monadic left fold of `World.step` (HOST's `staged_rooted` builds on it). -/
theorem fold_foldlM {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)},
      World.fold E w l = .ok w' ↔ l.foldlM (World.step E) w = .ok w'
  | w, w', [] => by simp [World.fold, List.foldlM, pure, Except.pure]
  | w, w', t :: rest => by
      rw [fold_cons_ok, List.foldlM_cons]
      cases ha : World.step E w t with
      | error r => simp [bind, Except.bind]
      | ok w₁ => simp [bind, Except.bind, fold_foldlM]

/-- An admitted turn lands inside its window. -/
theorem admit_window {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : t.notBefore ≤ w.height + 1 ∧ w.height + 1 ≤ t.validUntil := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  have hw := hc.window
  unfold checkWindow at hw
  rw [req_ok] at hw
  simpa using hw

/-- A recorded refusal was recorded inside its call's window (KERNEL-47 amendment 5). -/
theorem refuse_window {E : Env D} {w w' : World D} {r : Refused D}
    (h : World.refuse E w r = .ok w') : r.notBefore ≤ w.height + 1 ∧ w.height + 1 ≤ r.validUntil := by
  obtain ⟨hc, _⟩ := refuse_ok h
  unfold checkRefusal at hc
  simp only [except_bind_ok] at hc
  obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, hw, -⟩ := hc
  have := req_ok.mp hw
  simpa using this

end Nanodregg.Kernel
