/-
# Kernel.Proofs.Origin — a World is its origin, and a call is bound to one World (KERNEL-24)

* `admit_origin`, `fold_origin`: no Turn changes the origin.
* `genesis_inj`: two geneses with one origin were made from the same name, nonce, allowance and
  founders, or their two origin inputs collide (`originPre`); `genesis_chain_inj`: the same for the
  genesis chain (one more hash, `World.genesisPre`). Teeth `genesis_inj_sep`, `genesis_chain_inj_sep`:
  where the hash separates the two inputs, the equality alone.
* `admitted_elsewhere_refused`: a call one World admitted is, on any World with another origin,
  refused `wrongWorld` (or, if that World's journal holds the same transaction id, `replayed`;
  either way never admitted).
-/
import Kernel.Proofs.Lawful
import Kernel.Proofs.Fold
import Kernel.Proofs.Refuse
import Kernel.Proofs.Receive
import Kernel.Receive.Follow
import Codec.Proofs.Raw

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Stream

variable {D : Type} [Ord D] [DecidableEq D]

theorem admit_origin {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    w'.origin = w.origin := by
  unfold World.admit at h
  split at h
  · cases h; rfl
  · cases h

theorem fold_origin {E : Env D} {w w' : World D} {l : List (Step D)} (h : World.fold E w l = .ok w') :
    w'.origin = w.origin :=
  fold_keeps (P := fun v => v.origin = w.origin) (fun hp ha => (admit_origin ha).trans hp)
    (fun hp hr => (refuse_frame hr).2.2.2.2.trans hp) rfl h

theorem genesis_origin (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) :
    (genesisWorld X name nonce allowance founders auth).origin = originOf X name nonce allowance founders auth := rfl

theorem genesis_chain (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) :
    (genesisWorld X name nonce allowance founders auth).chain =
      World.genesisChain X.env (genesisWorld X name nonce allowance founders auth).origin := rfl

/-- An authority one cell carries and somebody can meet: at most `slotsPerCellMax - 2` certifiers,
each key within the raw codec's bound, no key twice (a quorum counts distinct keys), the threshold
within the count and zero only when nobody is listed (`Authority.none`). -/
def Authority.Fits (a : Authority) : Prop :=
  a.certifiers.length + 2 ≤ Bounds.slotsPerCellMax ∧ (∀ k ∈ a.certifiers, k.size ≤ Bounds.eventBytesMax) ∧
    a.certifiers.Nodup ∧ (a.threshold ≤ a.certifiers.length ∧ (a.threshold = 0 → a.certifiers = []))

/-- A genesis input within the raw codec's bounds (every length at most `Bounds.eventBytesMax`) whose
allowance plus the genesis World's storage is below 2^64 (so the allowance is, and `fold_conserves`
keeps the sum below it on every World the genesis reaches: `Budget.fold_budget_lt`). `genesis`
refuses by name outside it (`genesis_ok`). -/
def GenesisFits (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) : Prop :=
  name.size ≤ Bounds.eventBytesMax ∧ nonce.size ≤ Bounds.eventBytesMax ∧
    founders.length ≤ Bounds.eventBytesMax ∧
    (∀ f ∈ founders, f.1.size ≤ Bounds.eventBytesMax ∧ (X.env.bytes f.2).size ≤ Bounds.eventBytesMax) ∧
    auth.Fits ∧
    (genesisWorld X name nonce allowance founders auth).weight + allowance < 2 ^ 64

omit [Ord D] [DecidableEq D] in
/-- Distinct refusals have distinct wire names: equal names, same constructor. -/
theorem GenesisRefusal.name_injective (a b : GenesisRefusal) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [GenesisRefusal.name] <;> rfl

theorem req_bind_ok {ε β : Type} {b : Bool} {e : ε} {f : Unit → Except ε β} {x : β} :
    (req b e >>= f) = .ok x ↔ b = true ∧ f () = .ok x := by
  cases b <;> simp [req, bind, Except.bind]

omit [Ord D] [DecidableEq D] in
theorem checkFounders_ok {X : Ctx D} : ∀ {i : Nat} {fs : List (ByteArray × D)},
    checkFounders X i fs = .ok () ↔
      ∀ f ∈ fs, f.1.size ≤ Bounds.eventBytesMax ∧ (X.env.bytes f.2).size ≤ Bounds.eventBytesMax
  | _, [] => by simp [checkFounders]
  | i, f :: rest => by
      simp only [checkFounders, req_bind_ok, decide_eq_true_eq, List.mem_cons, forall_eq_or_imp]
      rw [checkFounders_ok, and_assoc]

omit [Ord D] [DecidableEq D] in
theorem checkCertifiers_ok : ∀ {i : Nat} {seen ks : List ByteArray},
    checkCertifiers i seen ks = .ok () ↔
      (∀ k ∈ ks, k.size ≤ Bounds.eventBytesMax) ∧ ks.Nodup ∧ ∀ k ∈ ks, k ∉ seen
  | _, _, [] => by simp [checkCertifiers]
  | i, seen, k :: rest => by
      simp only [checkCertifiers, req_bind_ok, decide_eq_true_eq, List.all_eq_true, List.mem_cons,
        forall_eq_or_imp, List.nodup_cons]
      rw [checkCertifiers_ok]
      constructor
      · rintro ⟨hs, hn, hr, hd, hseen⟩
        exact ⟨⟨hs, hr⟩, ⟨fun hk => hseen k hk List.mem_cons_self, hd⟩, fun h => hn k h rfl,
          fun k' hk' h => hseen k' hk' (List.mem_cons_of_mem _ h)⟩
      · rintro ⟨⟨hs, hr⟩, ⟨hk, hd⟩, hn, hseen⟩
        refine ⟨hs, fun s hs' hks => hn (by subst hks; exact hs'), hr, hd, fun k' hk' h => ?_⟩
        rcases List.mem_cons.mp h with rfl | h
        · exact hk hk'
        · exact hseen k' hk' h

/-- **The genesis check is `GenesisFits`**, clause by clause. -/
theorem checkGenesis_ok {X : Ctx D} {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    {auth : Authority} :
    checkGenesis X name nonce allowance founders auth = .ok () ↔ GenesisFits X name nonce allowance founders auth := by
  have hc : Bounds.counterLimit = 2 ^ 64 := by decide
  simp only [checkGenesis, req_bind_ok, decide_eq_true_eq, hc]
  simp only [except_bind_ok, req_ok, decide_eq_true_eq]
  unfold GenesisFits Authority.Fits
  constructor
  · rintro ⟨h1, h2, h3, h6, h8, ⟨⟩, h4, ⟨⟩, h7, h5⟩
    obtain ⟨h7a, h7b, -⟩ := checkCertifiers_ok.mp h7
    exact ⟨h1, h2, h3, checkFounders_ok.mp h4, ⟨h6, h7a, h7b, h8⟩, h5⟩
  · rintro ⟨h1, h2, h3, h4, ⟨h6, h7a, h7b, h8⟩, h5⟩
    exact ⟨h1, h2, h3, h6, h8, (), checkFounders_ok.mpr h4, (), checkCertifiers_ok.mpr ⟨h7a, h7b, by simp⟩, h5⟩

/-- **Genesis is checked** (KERNEL-31): it returns a World exactly on a `GenesisFits` input, and
that World is `genesisWorld`. Every theorem about `genesisWorld` is a theorem about what `genesis`
returns; `genesis_inj`'s premises hold for every genesis that returned. -/
theorem genesis_ok {X : Ctx D} {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    {auth : Authority} {w : World D} :
    genesis X name nonce allowance founders auth = .ok w ↔
      GenesisFits X name nonce allowance founders auth ∧ w = genesisWorld X name nonce allowance founders auth := by
  unfold genesis
  rw [except_bind_ok]
  constructor
  · rintro ⟨⟨⟩, hc, hw⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hw
    exact ⟨checkGenesis_ok.mp hc, hw.symm⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨(), checkGenesis_ok.mpr hf, rfl⟩

theorem genesisInput_lawfulOn :
    LawfulOn (fun v : GenesisInput => v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1 < 2 ^ 64 ∧ ((v.2.2.2.1.length ≤ Bounds.eventBytesMax ∧
        ∀ x ∈ v.2.2.2.1, x.1.size ≤ Bounds.eventBytesMax ∧ x.2.size ≤ Bounds.eventBytesMax) ∧
        ((v.2.2.2.2.1.length ≤ Bounds.eventBytesMax ∧ ∀ x ∈ v.2.2.2.2.1, x.size ≤ Bounds.eventBytesMax) ∧
          v.2.2.2.2.2 < 2 ^ 64))))) genesisInput :=
  product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
    (product_lawfulOn nat64_lawfulOn (product_lawfulOn (rawList_lawfulOn (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (rawBytes_lawfulOn _ (by decide))) _ (by decide))
      (product_lawfulOn (rawList_lawfulOn (rawBytes_lawfulOn _ (by decide)) _ (by decide)) nat64_lawfulOn))))

theorem inputOf_fits {X : Ctx D} {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    {auth : Authority} (h : GenesisFits X name nonce allowance founders auth) :
    let v := inputOf X name nonce allowance founders auth
    v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1 < 2 ^ 64 ∧ ((v.2.2.2.1.length ≤ Bounds.eventBytesMax ∧
        ∀ x ∈ v.2.2.2.1, x.1.size ≤ Bounds.eventBytesMax ∧ x.2.size ≤ Bounds.eventBytesMax) ∧
        ((v.2.2.2.2.1.length ≤ Bounds.eventBytesMax ∧ ∀ x ∈ v.2.2.2.2.1, x.size ≤ Bounds.eventBytesMax) ∧
          v.2.2.2.2.2 < 2 ^ 64)))) := by
  obtain ⟨h1, h2, h4, h5, ⟨ha1, ha2, -, ha4, -⟩, h3⟩ := h
  have hs1 : Bounds.slotsPerCellMax = 1024 := rfl
  have hs2 : Bounds.eventBytesMax = 65536 := rfl
  refine ⟨h1, h2, by simp only [inputOf]; omega, ⟨by simpa [inputOf] using h4, ?_⟩,
    ⟨by simp only [inputOf]; omega, fun x hx => ha2 x hx⟩, by simp only [inputOf]; omega⟩
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

theorem ba_append_cancel (a x y : ByteArray) (h : a ++ x = a ++ y) : x = y := by
  have hd : a.data ++ x.data = a.data ++ y.data := by
    have := congrArg ByteArray.data h
    simpa [ByteArray.data_append] using this
  exact ByteArray.ext (Array.append_right_inj _ |>.mp hd)

theorem sum_bytes_inl_on {α β : Type} {P : α → Prop} {a : Stream α} {c : Stream β} (ha : LawfulOn P a) (v : α) :
    (sum a c).bytes (.inl v) = u8.bytes 0 ++ a.bytes v := by
  simp only [Stream.bytes, sum]
  rw [ha.put_eq]; rfl

theorem sum_bytes_inr_on {α β : Type} {Q : β → Prop} {a : Stream α} {c : Stream β} (hc : LawfulOn Q c) (v : β) :
    (sum a c).bytes (.inr v) = u8.bytes 1 ++ c.bytes v := by
  simp only [Stream.bytes, sum]
  rw [hc.put_eq]; rfl

/-- A sum's two cases never share bytes: the first byte is the case. -/
theorem sum_inl_ne_inr {α β : Type} {P : α → Prop} {Q : β → Prop} {a : Stream α} {c : Stream β}
    (ha : LawfulOn P a) (hc : LawfulOn Q c) (v : α) (w : β) :
    (sum a c).bytes (.inl v) ≠ (sum a c).bytes (.inr w) := by
  rw [sum_bytes_inl_on ha, sum_bytes_inr_on hc]
  intro h
  have := congrArg (fun b : ByteArray => b.data[0]?) h
  simp only [ByteArray.data_append] at this
  rw [Array.getElem?_append_left (by simp [u8, Stream.bytes]),
    Array.getElem?_append_left (by simp [u8, Stream.bytes])] at this
  simp [u8, Stream.bytes] at this

/-- **Genesis commits to everything it was made from.** Two geneses with equal origins had equal
names, nonces, allowances and founders (keys and next-key digests, in order), or their two origin
inputs collide. -/
theorem genesis_inj {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {allowance allowance' : Nat}
    {founders founders' : List (ByteArray × D)} {auth auth' : Authority}
    (hf : GenesisFits X name nonce allowance founders auth) (hf' : GenesisFits X name' nonce' allowance' founders' auth')
    (h : originOf X name nonce allowance founders auth = originOf X name' nonce' allowance' founders' auth') :
    (name = name' ∧ nonce = nonce' ∧ allowance = allowance' ∧ founders = founders' ∧ auth = auth') ∨
      CollidesAmong X.env.hash
        [originPre X name nonce allowance founders auth, originPre X name' nonce' allowance' founders' auth'] := by
  by_cases hbytes : originInput.bytes (.inl (inputOf X name nonce allowance founders auth)) =
      originInput.bytes (.inl (inputOf X name' nonce' allowance' founders' auth'))
  · left
    unfold originInput at hbytes
    rw [sum_bytes_inl_on genesisInput_lawfulOn, sum_bytes_inl_on genesisInput_lawfulOn] at hbytes
    have he := genesisInput_lawfulOn.bytes_injective (inputOf_fits hf) (inputOf_fits hf')
      (ba_append_cancel _ _ _ hbytes)
    simp only [inputOf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, hl, hc, ht⟩ := he
    refine ⟨rfl, rfl, rfl, ?_, by cases auth; cases auth'; cases hc; cases ht; rfl⟩
    have hinj : Function.Injective (fun f : ByteArray × D => (f.1, X.env.bytes f.2)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 (hE.bytes_eq hab.2)
    exact map_inj hinj hl
  · right
    exact .pair (fun he => hbytes (congrArg Prod.snd he)) h

omit [DecidableEq D] in
/-- **The genesis chain commits to the origin** (one more hash): equal genesis chains, equal
origins, or the two genesis inputs collide. With `genesis_inj`, equal genesis chains mean equal
inputs, up to two collisions. -/
theorem genesis_chain_inj {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {o o' : D} (h : X.env.hash domGenesis (X.env.bytes o) = X.env.hash domGenesis (X.env.bytes o')) :
    o = o' ∨ CollidesAmong X.env.hash [World.genesisPre X.env o, World.genesisPre X.env o'] := by
  by_cases he : X.env.bytes o = X.env.bytes o'
  · exact .inl (hE.bytes_eq he)
  · exact .inr (.pair (fun e => he (congrArg Prod.snd e)) h)

/-- **Tooth of `genesis_inj`**: where the hash separates the two origin inputs, equal origins are
equal genesis inputs. -/
theorem genesis_inj_sep {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {allowance allowance' : Nat}
    {founders founders' : List (ByteArray × D)} {auth auth' : Authority}
    (hf : GenesisFits X name nonce allowance founders auth) (hf' : GenesisFits X name' nonce' allowance' founders' auth')
    (hs : Separates X.env.hash
      [originPre X name nonce allowance founders auth, originPre X name' nonce' allowance' founders' auth'])
    (h : originOf X name nonce allowance founders auth = originOf X name' nonce' allowance' founders' auth') :
    name = name' ∧ nonce = nonce' ∧ allowance = allowance' ∧ founders = founders' ∧ auth = auth' :=
  hs.elim (genesis_inj hE hf hf' h)

omit [DecidableEq D] in
/-- **Tooth of `genesis_chain_inj`**: where the hash separates the two genesis inputs, equal genesis
chains are equal origins. -/
theorem genesis_chain_inj_sep {X : Ctx D} {n : Nat} (hE : X.env.Lawful n) {o o' : D}
    (hs : Separates X.env.hash [World.genesisPre X.env o, World.genesisPre X.env o'])
    (h : X.env.hash domGenesis (X.env.bytes o) = X.env.hash domGenesis (X.env.bytes o')) : o = o' :=
  hs.elim (genesis_chain_inj hE h)


/-- **A call is bound to one World.** A call that one World admitted is never admitted by a World
with another origin: it is refused `wrongWorld`, or, if that World's journal already holds its
transaction id, rejected `replayed`. -/
theorem admitted_elsewhere_refused {X : Ctx D} {w₁ w₁' w₂ : World D} {c : Call D} {t : Turn D}
    (h : submit X w₁ c = .ok (t, w₁')) (hne : w₂.origin ≠ w₁.origin) :
    submit X w₂ c = .error (.refused .wrongWorld) ∨
      (∃ ht, submit X w₂ c = .error (.rejected (.replayed ht))) ∨
      ∃ code, submit X w₂ c = .error (.rejected (.refusedFinal code)) := by
  obtain ⟨_, hr, _⟩ := submit_ok h
  have hw : c.unsigned.world ≠ w₂.origin := by
    rw [(receive_ok_with hr).1]; exact fun e => hne e.symm
  cases hj : w₂.journalAt X.env (txIdOf X c) with
  | some p => exact .inr (.inl ⟨p.1, submit_replayed hj⟩)
  | none =>
      cases hq : refusedAnswer X w₂ c with
      | some code => exact .inr (.inr ⟨code, by unfold submit; rw [hj, hq]⟩)
      | none =>
          left
          unfold submit
          rw [hj, hq]
          simp [signedBy, req, hw, bind, Except.bind]

end Nanodregg.Kernel.Receive
