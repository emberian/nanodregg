/-
# Kernel.Proofs.Origin — a World is its origin, and a call is bound to one World (KERNEL-24)

* `admit_origin`, `fold_origin`: no Turn changes the origin.
* `genesis_inj`: two geneses with one origin were made from the same name, nonce, allowance and
  founders, or the origin hash has a collision; `genesis_chain_inj`: the same for the genesis
  chain (one more hash).
* `admitted_elsewhere_refused`: a call one World admitted is, on any World with another origin,
  refused `wrongWorld` (or, if that World's journal holds the same transaction id, `replayed`;
  either way never admitted).
-/
import Kernel.Proofs.Receive
import Kernel.Receive.Follow
import Codec.Proofs.Raw

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Stream

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- A collision of the hash under one domain: two byte strings, one digest. -/
def HashColl (E : Env D) (dom : String) : Prop := ∃ a b : ByteArray, a ≠ b ∧ E.hash dom a = E.hash dom b

theorem admit_origin {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    w'.origin = w.origin := by
  unfold World.admit at h
  split at h
  · cases h; rfl
  · cases h

theorem fold_origin {E : Env D} : ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
    w'.origin = w.origin
  | _, _, [], h => by cases h; rfl
  | w, w', t :: rest, h => by
      unfold World.fold at h
      split at h
      · rename_i w₁ h₁
        split at h
        · cases h; rename_i h₂; exact (fold_origin h₂).trans (admit_origin h₁)
        · cases h
      · cases h

omit [DecidableEq D] in
theorem genesis_origin (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    (genesis X name nonce allowance founders).origin = originOf X name nonce allowance founders := rfl

omit [DecidableEq D] in
theorem genesis_chain (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    (genesis X name nonce allowance founders).chain =
      World.genesisChain X.env (genesis X name nonce allowance founders).origin := rfl

/-- A genesis input within the raw codec's bounds (every length at most `Bounds.eventBytesMax`,
the allowance below 2^64). HOST's `host genesis` refuses a NAME past it. -/
def GenesisFits (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) : Prop :=
  name.size ≤ Bounds.eventBytesMax ∧ nonce.size ≤ Bounds.eventBytesMax ∧ allowance < 2 ^ 64 ∧
    founders.length ≤ Bounds.eventBytesMax ∧
      ∀ f ∈ founders, f.1.size ≤ Bounds.eventBytesMax ∧ (X.env.bytes f.2).size ≤ Bounds.eventBytesMax

theorem genesisInput_lawfulOn :
    LawfulOn (fun v : GenesisInput => v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1 < 2 ^ 64 ∧ (v.2.2.2.length ≤ Bounds.eventBytesMax ∧
        ∀ x ∈ v.2.2.2, x.1.size ≤ Bounds.eventBytesMax ∧ x.2.size ≤ Bounds.eventBytesMax)))) genesisInput :=
  product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
    (product_lawfulOn nat64_lawfulOn (rawList_lawfulOn (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (rawBytes_lawfulOn _ (by decide))) _ (by decide))))

omit [Ord D] [DecidableEq D] in
theorem inputOf_fits {X : Ctx D} {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    (h : GenesisFits X name nonce allowance founders) :
    let v := inputOf X name nonce allowance founders
    v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1 < 2 ^ 64 ∧ (v.2.2.2.length ≤ Bounds.eventBytesMax ∧
        ∀ x ∈ v.2.2.2, x.1.size ≤ Bounds.eventBytesMax ∧ x.2.size ≤ Bounds.eventBytesMax))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by simpa [inputOf] using h4, ?_⟩
  intro x hx
  simp only [inputOf, List.mem_map] at hx
  obtain ⟨f, hf, rfl⟩ := hx
  exact h5 f hf

theorem map_inj {α β : Type} {f : α → β} (hf : Function.Injective f) :
    ∀ {l l' : List α}, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf h.1, map_inj hf h.2]

omit [Ord D] [DecidableEq D] in
/-- **Genesis commits to everything it was made from.** Two geneses with equal origins had equal
names, nonces, allowances and founders (keys and next-key digests, in order), or the origin hash
has a collision. -/
theorem genesis_inj {X : Ctx D} (hb : ∀ a b : D, X.env.bytes a = X.env.bytes b → a = b)
    {name nonce name' nonce' : ByteArray} {allowance allowance' : Nat}
    {founders founders' : List (ByteArray × D)}
    (hf : GenesisFits X name nonce allowance founders) (hf' : GenesisFits X name' nonce' allowance' founders')
    (h : originOf X name nonce allowance founders = originOf X name' nonce' allowance' founders') :
    (name = name' ∧ nonce = nonce' ∧ allowance = allowance' ∧ founders = founders') ∨
      HashColl X.env domOrigin := by
  by_cases hbytes : genesisInput.bytes (inputOf X name nonce allowance founders) =
      genesisInput.bytes (inputOf X name' nonce' allowance' founders')
  · left
    have he := genesisInput_lawfulOn.bytes_injective (inputOf_fits hf) (inputOf_fits hf') hbytes
    simp only [inputOf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, hl⟩ := he
    refine ⟨rfl, rfl, rfl, ?_⟩
    have hinj : Function.Injective (fun f : ByteArray × D => (f.1, X.env.bytes f.2)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 (hb _ _ hab.2)
    exact map_inj hinj hl
  · right
    exact ⟨_, _, hbytes, h⟩

omit [Ord D] [DecidableEq D] in
/-- **The genesis chain commits to the origin** (one more hash): equal genesis chains, equal
origins, or a collision of the genesis hash. With `genesis_inj`, equal genesis chains mean equal
inputs, up to two collisions. -/
theorem genesis_chain_inj {X : Ctx D} (hb : ∀ a b : D, X.env.bytes a = X.env.bytes b → a = b)
    {o o' : D} (h : X.env.hash domGenesis (X.env.bytes o) = X.env.hash domGenesis (X.env.bytes o')) :
    o = o' ∨ HashColl X.env domGenesis := by
  by_cases he : X.env.bytes o = X.env.bytes o'
  · exact .inl (hb _ _ he)
  · exact .inr ⟨_, _, he, h⟩


/-- **A call is bound to one World.** A call that one World admitted is never admitted by a World
with another origin: it is refused `wrongWorld`, or, if that World's journal already holds its
transaction id, rejected `replayed`. -/
theorem admitted_elsewhere_refused {X : Ctx D} {w₁ w₁' w₂ : World D} {c : Call D} {t : Turn D}
    (h : submit X w₁ c = .ok (t, w₁')) (hne : w₂.origin ≠ w₁.origin) :
    submit X w₂ c = .error (.refused .wrongWorld) ∨
      ∃ ht, submit X w₂ c = .error (.rejected (.replayed ht)) := by
  obtain ⟨_, hr, _⟩ := submit_ok h
  have hw : c.unsigned.world ≠ w₂.origin := by
    rw [(receive_ok_with hr).1]; exact fun e => hne e.symm
  cases hj : w₂.journal[txIdOf X c]? with
  | some p => exact .inr ⟨p.1, submit_replayed hj⟩
  | none =>
      left
      unfold submit
      rw [hj]
      simp only [receive_wrongWorld hw]

end Nanodregg.Kernel.Receive
