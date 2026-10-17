/-
# Kernel.Proofs.Rooted — every World grant is rooted at genesis (KERNEL-20's open invariant)

`grant_rooted` says one derivation never roots a World grant. This module lifts that to every
World an honest log reaches: `WorldRooted R w` — every live grant cell is append-only, names a
target, and, when its target is the World, has a parent or is one of the roots `R` (the founders'
genesis grants). It holds at genesis (`genesis_rooted`), every derive-then-admit step keeps it
(`submit_rooted`, `step_rooted`), so every audited log keeps it (`audit_rooted`); and a chain for a
World right through such a World then ends at a root in `R` (`chain_rooted`).

The kernel half is structural: an append-only cell never loses or changes a slot (`postWrite`),
so a write can neither strip a grant's parent nor retarget it, whoever the receiver is.
-/
import Kernel.Proofs.Authority
import Kernel.Proofs.Audit
import Kernel.Proofs.Frame
import Kernel.Receive.Follow

namespace Nanodregg.Kernel

/-! ## Slots -/

theorem slots_get_set_eq (k : Nat) (v : ByteArray) : ∀ s : Slots, (s.set k v).get k = some v
  | [] => by simp [Slots.set, Slots.get]
  | (k', v') :: rest => by
      unfold Slots.set
      split
      · simp [Slots.get]
      · split
        · simp [Slots.get]
        · rename_i h1 h2
          have := slots_get_set_eq k v rest
          simp only [Slots.get, List.lookup] at this ⊢
          have : (k == k') = false := by simpa using h2
          simp [*]

theorem slots_get_set_ne {k k' : Nat} (v : ByteArray) (hne : k ≠ k') :
    ∀ s : Slots, (s.set k' v).get k = s.get k
  | [] => by
      have hb : (k == k') = false := by simpa using hne
      simp [Slots.set, Slots.get, List.lookup, hb]
  | (k'', v'') :: rest => by
      have hb : (k == k') = false := by simpa using hne
      unfold Slots.set
      split
      · simp [Slots.get, List.lookup, hb]
      · split
        · rename_i _ h; subst h; simp [Slots.get, List.lookup, hb]
        · have := slots_get_set_ne v hne rest
          simp only [Slots.get, List.lookup] at this ⊢
          split <;> simp_all

/-- What a fold of `set`s leaves at a key: the last pair for it, else what was there. -/
theorem foldl_set_get (k : Nat) : ∀ (ps : List (Nat × ByteArray)) (s0 : Slots),
    (ps.foldl (fun s p => s.set p.1 p.2) s0).get k =
      match (ps.filter fun p => p.1 == k).getLast? with
      | some p => some p.2
      | none => s0.get k
  | [], s0 => by simp
  | p :: rest, s0 => by
      simp only [List.foldl_cons]
      rw [foldl_set_get k rest (s0.set p.1 p.2)]
      cases hr : (rest.filter fun p => p.1 == k).getLast? with
      | some q =>
          have hne : rest.filter (fun p => p.1 == k) ≠ [] := by
            intro h; rw [h] at hr; simp at hr
          by_cases hp : p.1 = k
          · simp only [List.filter_cons, hp, beq_self_eq_true, if_true]
            rw [List.getLast?_cons, hr]; rfl
          · have : (p.1 == k) = false := by simpa using hp
            simp only [List.filter_cons, this, Bool.false_eq_true, if_false]; rw [hr]
      | none =>
          have he : rest.filter (fun p => p.1 == k) = [] := by
            cases h : rest.filter (fun p => p.1 == k) with
            | nil => rfl
            | cons a l => rw [h] at hr; simp at hr
          by_cases hp : p.1 = k
          · subst hp
            simp only [List.filter_cons, beq_self_eq_true, if_true, he]
            simp [slots_get_set_eq]
          · have : (p.1 == k) = false := by simpa using hp
            simp only [List.filter_cons, this, Bool.false_eq_true, if_false, he]
            simp [slots_get_set_ne _ (Ne.symm hp)]

theorem applyOps_keep {k : Nat} {v : ByteArray} :
    ∀ (ops : List Op) (s : Slots), (∀ o ∈ ops, ∃ k' v', o = .set k' v' ∧ k' ≠ k) →
      s.get k = some v → (applyOps s ops).get k = some v
  | [], s, _, h => h
  | o :: rest, s, hops, h => by
      obtain ⟨k', v', rfl, hne⟩ := hops o (by simp)
      show (applyOps (applyOp s (.set k' v')) rest).get k = some v
      apply applyOps_keep rest _ (fun o ho => hops o (by simp [ho]))
      simp only [applyOp]
      rw [slots_get_set_ne _ (Ne.symm hne)]; exact h

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- A write keeps a cell's kind and discipline, and an append-only cell keeps every slot it had. -/
theorem postWrite_keeps {c : D} {cell post : Cell} {ops : List Op}
    (h : postWrite c cell ops = .ok post) :
    post.kind = cell.kind ∧ post.discipline = cell.discipline ∧
      (cell.discipline = .appendOnly → ∀ k v, cell.slots.get k = some v → post.slots.get k = some v) := by
  unfold postWrite at h
  split at h
  · simp at h
  · rename_i hd
    simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨⟩, hf, ⟨⟩, _, rfl⟩ := h
    refine ⟨rfl, rfl, fun _ k v hk => applyOps_keep ops cell.slots ?_ hk⟩
    intro o ho
    have := (forEx_ok.mp hf) o ho
    cases o with
    | set k' v' =>
        refine ⟨k', v', rfl, ?_⟩
        rintro rfl
        rw [req_ok] at this
        simp [hk] at this
    | erase k' => simp at this
  · rename_i hd
    simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨⟩, _, rfl⟩ := h
    refine ⟨rfl, rfl, fun ha => ?_⟩
    rw [hd] at ha; cases ha
  · rename_i hd
    simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨⟩, _, ⟨⟩, _, rfl⟩ := h
    refine ⟨rfl, rfl, fun ha => ?_⟩
    rw [hd] at ha; cases ha

section Admit
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [DecidableEq D] in
theorem insertAll_get_some {k : D} {e : Entry} :
    ∀ {m : Std.TreeMap D Entry compare} {ps : List (D × Entry)}, (insertAll m ps)[k]? = some e →
      (k, e) ∈ ps ∨ (k ∉ ps.map Prod.fst ∧ m[k]? = some e)
  | m, [], h => .inr ⟨by simp, h⟩
  | m, p :: rest, h => by
      rcases insertAll_get_some (m := m.insert p.1 p.2) (ps := rest) h with hr | ⟨hn, hm⟩
      · exact .inl (by simp [hr])
      · rw [Std.TreeMap.getElem?_insert] at hm
        split at hm
        · rename_i he
          have := Std.LawfulEqCmp.eq_of_compare he
          subst this
          simp only [Option.some.injEq] at hm
          subst hm
          exact .inl (by simp)
        · rename_i hne
          refine .inr ⟨?_, hm⟩
          simp only [List.map_cons, List.mem_cons, not_or]
          refine ⟨fun h => hne ?_, hn⟩
          rw [h]; exact Std.ReflCmp.compare_self

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A touch that leaves a live cell behind wrote it: from a live cell, by `postWrite`. -/
theorem touchCheck_live {E : Env D} {w : World D} {x : Touch D} {p : Post D} {c' : Cell}
    (h : touchCheck E w x = .ok (some p)) (he : p.entry = .live c') :
    p.cell = x.cell ∧ ∃ cell ops, w.live x.cell = some cell ∧ x.act = .write ops ∧
      postWrite x.cell cell ops = .ok c' := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rw [ha] at h; simp [pure, Except.pure] at h
  | write ops =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨post, hp, rfl⟩ := h
          simp only [Entry.live.injEq] at he
          subst he
          exact ⟨rfl, cell, ops, rfl, rfl, hp⟩
  | retire =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp at he

/-- Every live cell after an admitted turn was born by it, or was live before and is either
untouched or what a write of it left. -/
theorem admit_live {E : Env D} {w w' : World D} {t : Turn D} {id : D} {c' : Cell}
    (h : World.admit E w t = .ok w') (hl : w'.live id = some c') :
    c' ∈ t.creates ∨ ∃ cell, w.live id = some cell ∧
      (c' = cell ∨ ∃ ops, postWrite id cell ops = .ok c') := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  have hg : (commit E w t posts).cells[id]? = some (.live c') := by
    unfold World.live at hl; split at hl
    · rename_i hh; simp only [Option.some.injEq] at hl; rw [hh, hl]
    · simp at hl
  rcases insertAll_get_some hg with hb | ⟨_, hm⟩
  · left
    unfold bornEntries createdPairs at hb
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hb
    simp only [Prod.mk.injEq, Entry.live.injEq] at hqe
    rw [← hqe.2]; exact List.of_mem_zip hq |>.2
  · right
    rcases insertAll_get_some hm with hp | ⟨_, hw⟩
    · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hp
      simp only [Post.pair, Prod.mk.injEq] at hpe
      obtain ⟨raw, hm', rfl⟩ := hk.touches
      have hp' : some p ∈ raw := by simpa [List.reduceOption, List.mem_filterMap] using hp
      obtain ⟨x, _, hr⟩ := mapEx_mem hm' (some p) hp'
      obtain ⟨hpc, cell, ops, hc, _, hw⟩ := touchCheck_live hr hpe.2
      rw [← hpe.1, hpc]
      exact ⟨cell, hc, .inr ⟨ops, hw⟩⟩
    · exact ⟨c', by unfold World.live; rw [hw], .inl rfl⟩

end Admit

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- Every live grant is append-only and names a target; a grant on the World has a parent unless
it is one of the roots `R`. -/
def WorldRooted (X : Ctx D) (R : D → Prop) (w : World D) : Prop :=
  ∀ id cell, w.live id = some cell → cell.kind = kindGrant →
    cell.discipline = .appendOnly ∧ (cell.slots.get grantTarget).isSome = true ∧
      (cell.slots.get grantTarget = some (X.env.bytes (worldId X)) →
        (cell.slots.get grantParent).isSome = true ∨ R id)

/-- What a born grant must be for the World to stay rooted: append-only, targeted, and parented
when its target is the World. -/
def BornRooted (X : Ctx D) (cell : Cell) : Prop :=
  cell.kind = kindGrant → cell.discipline = .appendOnly ∧ (cell.slots.get grantTarget).isSome = true ∧
    (cell.slots.get grantTarget = some (X.env.bytes (worldId X)) → (cell.slots.get grantParent).isSome = true)

section Step
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **The kernel keeps a World rooted** whatever turn it admits, given rooted births: a write to
an append-only grant cannot strip its parent or move its target. -/
theorem admit_rooted {X : Ctx D} {R : D → Prop} {w w' : World D} {t : Turn D}
    (hw : WorldRooted X R w) (hb : ∀ c ∈ t.creates, BornRooted X c)
    (h : World.admit X.env w t = .ok w') : WorldRooted X R w' := by
  intro id c' hl hk
  rcases admit_live h hl with hc | ⟨cell, hold, rfl | ⟨ops, hp⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hb c' hc hk
    exact ⟨h1, h2, fun ht => .inl (h3 ht)⟩
  · exact hw id _ hold hk
  · obtain ⟨hkind, hdisc, hkeep⟩ := postWrite_keeps hp
    obtain ⟨h1, h2, h3⟩ := hw id cell hold (hkind ▸ hk)
    have keep := hkeep h1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h2
    have hv' := keep _ _ hv
    refine ⟨hdisc ▸ h1, by rw [hv']; rfl, fun ht => ?_⟩
    rw [hv'] at ht
    rcases h3 (hv.trans ht) with hp' | hr
    · left
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hp'
      rw [keep _ _ hu]; rfl
    · exact .inr hr

end Step

/-! ## Every receiver's births are rooted -/

omit [Ord D] [DecidableEq D] in
theorem rightSlots_keys (rights : List Right) : ∀ q ∈ rightSlots rights, 16 ≤ q.1 := by
  intro q hq
  unfold rightSlots at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
    cases r <;> simp [rightKey, enrollBase, invokeBase] <;> omega
  · split at hq
    · simp at hq; subst hq; simp [enrollBase]
    · simp at hq

omit [Ord D] [DecidableEq D] in
theorem slotsOf_get (ps : List (Nat × ByteArray)) (k : Nat) :
    (slotsOf ps).get k = ((ps.filter fun p => p.1 == k).getLast?).map Prod.snd := by
  unfold slotsOf
  rw [foldl_set_get]
  cases (ps.filter fun p => p.1 == k).getLast? <;> rfl

omit [Ord D] [DecidableEq D] in
/-- The grant cell `grant` bears, read at its target and parent slots. -/
theorem grantCell_slots (X : Ctx D) (target grantee member : D) (parent : Option D)
    (rights : List Right) :
    let s := slotsOf ([(grantTarget, X.env.bytes target), (grantGrantee, X.env.bytes grantee),
      (grantIssuer, X.env.bytes member)] ++ (parent.map fun p => (grantParent, X.env.bytes p)).toList ++
      rightSlots rights)
    s.get grantTarget = some (X.env.bytes target) ∧ ((s.get grantParent).isSome = parent.isSome) := by
  intro s
  have hr : ∀ k, k < 16 → (rightSlots rights).filter (fun p => p.1 == k) = [] := by
    intro k hk
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    have := rightSlots_keys rights q hq
    simp only [beq_iff_eq]; omega
  constructor
  · show (slotsOf _).get grantTarget = _
    rw [slotsOf_get, List.filter_append, List.filter_append, hr _ (by decide)]
    cases parent <;> simp [grantTarget, grantGrantee, grantIssuer, grantParent]
  · show ((slotsOf _).get grantParent).isSome = _
    rw [slotsOf_get, List.filter_append, List.filter_append, hr _ (by decide)]
    cases parent <;> simp [grantTarget, grantGrantee, grantIssuer, grantParent]

theorem sealTurn_creates {X : Ctx D} {c : Call D} {cr : List Cell} {efs : List (D × Act)}
    {ns : List D} {t : Turn D} (h : sealTurn X c cr efs ns = .ok t) : t.creates = cr :=
  (sealTurn_ok h).2.2.2.2.2.2.2.1

/-- **No receiver bears an unrooted grant.** Only `grant` bears a grant cell, append-only, and on
the World only with a parent (`grant_rooted`). Needs the digest's bytes to be injective (a target
read back as the World's bytes IS the World). -/
theorem dispatch_born {X : Ctx D} {look : Pinned D} {c : Call D} {b : Body D} {t : Turn D}
    (hinj : ∀ a b : D, X.env.bytes a = X.env.bytes b → a = b)
    (h : dispatch X look c b = .ok t) : ∀ cell ∈ t.creates, BornRooted X cell := by
  have kind_ne : ∀ (cell : Cell) (cr : List Cell), cr = [cell] → cell.kind ≠ kindGrant →
      ∀ x ∈ cr, BornRooted X x := by
    intro cell cr hcr hk x hx; subst hcr; simp at hx; subst hx; intro h; exact absurd h hk
  cases b with
  | enroll key next possession via =>
      simp only [dispatch, enroll, except_bind_ok] at h
      obtain ⟨_, _, _, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]
      exact kind_ne _ _ rfl (by simp [kindMember, kindGrant])
  | rotate key next =>
      simp only [dispatch, rotate, except_bind_ok] at h
      obtain ⟨_, _, ⟨⟩, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | install pkg =>
      simp only [dispatch, install, except_bind_ok] at h
      obtain ⟨⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]
      exact kind_ne _ _ rfl (by simp [kindPackage, kindGrant])
  | create pkg laws state =>
      simp only [dispatch, create, except_bind_ok] at h
      obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]
      exact kind_ne _ _ rfl (by simp [objectCell, kindObject, kindGrant])
  | write obj edits via =>
      simp only [dispatch, write, except_bind_ok] at h
      obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | law obj laws via =>
      simp only [dispatch, law, except_bind_ok] at h
      obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | invoke obj method args budget via =>
      simp only [dispatch, invoke, except_bind_ok] at h
      obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | grant target grantee rights parent =>
      have hroot := grant_rooted (X := X) (look := look) (c := c) (target := target)
        (grantee := grantee) (rights := rights) (parent := parent) (t := t)
      simp only [dispatch] at h
      have h' := h
      unfold grant at h
      simp only [except_bind_ok] at h
      obtain ⟨_, _, _, _, h⟩ := h
      rw [sealTurn_creates h]
      intro x hx _
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨ht, hp⟩ := grantCell_slots X target grantee c.unsigned.member parent rights
      refine ⟨rfl, by simp only at ht ⊢; rw [ht]; rfl, fun hw => ?_⟩
      simp only at ht hp hw ⊢
      rw [ht] at hw
      have := hinj _ _ (Option.some.inj hw)
      rw [hp]; exact hroot h' (.inl this)
  | revoke g =>
      simp only [dispatch, revoke, except_bind_ok] at h
      obtain ⟨_, _, _, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | issue cap =>
      simp only [dispatch, issue, except_bind_ok] at h
      obtain ⟨⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]
      exact kind_ne _ _ rfl (by simp [accountCell, kindAccount, kindGrant])
  | account asset =>
      simp only [dispatch, account] at h
      rw [sealTurn_creates h]
      exact kind_ne _ _ rfl (by simp [accountCell, kindAccount, kindGrant])
  | transfer src dst amount via once =>
      simp only [dispatch, transfer, except_bind_ok] at h
      obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp
  | credit well acct amount via =>
      simp only [dispatch, credit, except_bind_ok] at h
      obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, h⟩ := h
      rw [sealTurn_creates h]; simp

theorem receiveWith_dispatch {X : Ctx D} {look : Pinned D} {c : Call D} {t : Turn D}
    (h : receiveWith X look c = .ok t) : dispatch X look c c.unsigned.body = .ok t := by
  unfold receiveWith at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, ⟨⟩, _, h⟩ := h
  exact h

section Steps
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **Derive-then-admit keeps the World rooted.** -/
theorem step_rooted {X : Ctx D} {R : D → Prop} {w w' : World D} {c : Call D} {t : Turn D}
    (hinj : ∀ a b : D, X.env.bytes a = X.env.bytes b → a = b) (hw : WorldRooted X R w)
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') : WorldRooted X R w' :=
  admit_rooted hw (dispatch_born hinj (receiveWith_dispatch (receive_ok_with hr).2)) ha

/-- **The Host keeps the World rooted**: every committed submission. -/
theorem submit_rooted {X : Ctx D} {R : D → Prop} {w w' : World D} {c : Call D} {t : Turn D}
    (hinj : ∀ a b : D, X.env.bytes a = X.env.bytes b → a = b) (hw : WorldRooted X R w)
    (h : submit X w c = .ok (t, w')) : WorldRooted X R w' := by
  obtain ⟨_, hr, ha⟩ := submit_ok h
  exact step_rooted hinj hw hr ha

/-- **Every audited log keeps the World rooted**: the follower's World too. -/
theorem audit_rooted {X : Ctx D} {R : D → Prop}
    (hinj : ∀ a b : D, X.env.bytes a = X.env.bytes b → a = b) :
    ∀ {w w' : World D} {l : List (Turn D)}, WorldRooted X R w → audit X w l = .ok w' →
      WorldRooted X R w'
  | w, w', [], hw, h => by simp [audit] at h; subst h; exact hw
  | w, w', t :: rest, hw, h => by
      unfold audit at h
      cases hs : auditStep X w t with
      | error f => simp [hs] at h
      | ok w₁ =>
          cases ha : audit X w₁ rest with
          | error e => simp [hs, ha] at h
          | ok w₂ =>
              simp only [hs, ha, Except.ok.injEq] at h
              subst h
              unfold auditStep at hs
              cases hd : rederive X w t with
              | error r => simp [hd] at hs
              | ok u =>
                  cases hadm : World.admit X.env w t with
                  | error r => simp [hd, hadm] at hs
                  | ok w₃ =>
                      simp only [hd, hadm, Except.ok.injEq] at hs
                      subst hs
                      obtain ⟨c, _, hr⟩ := rederive_ok.mp hd
                      exact audit_rooted hinj (step_rooted hinj hw hr hadm) ha

end Steps

/-! ## Genesis, and what rootedness buys -/

/-- The founders' genesis grants. -/
def GenesisRoot (X : Ctx D) (origin : D) (id : D) : Prop := ∃ i, id = founderGrantId X origin i

omit [Ord D] [DecidableEq D] in
theorem founderRoot_target (X : Ctx D) (m : D) :
    (founderRoot X m).slots.get grantTarget = some (X.env.bytes (worldId X)) := by
  have hr : (rightSlots [Right.observe, .enroll enrollMax]).filter (fun p => p.1 == grantTarget) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    have := rightSlots_keys _ q hq
    simp only [beq_iff_eq, grantTarget]; omega
  show (slotsOf _).get grantTarget = _
  rw [slotsOf_get, List.filter_append, hr]
  simp [grantTarget, grantGrantee, grantIssuer]

section Genesis
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [DecidableEq D] in
/-- **Genesis is rooted**, its roots the founders' grants. -/
theorem genesis_rooted (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) :
    WorldRooted X (GenesisRoot X (originOf X name nonce allowance founders))
      (genesis X name nonce allowance founders) := by
  let o := originOf X name nonce allowance founders
  let P : Std.TreeMap D Entry compare → Prop := fun m => ∀ id cell, m[id]? = some (.live cell) →
    cell.kind = kindGrant → cell.discipline = .appendOnly ∧ (cell.slots.get grantTarget).isSome = true ∧
      (cell.slots.get grantTarget = some (X.env.bytes (worldId X)) →
        (cell.slots.get grantParent).isSome = true ∨ GenesisRoot X o id)
  have step : ∀ (l : List ((ByteArray × D) × Nat)) (m : Std.TreeMap D Entry compare), P m →
      P (l.foldl (fun (m : Std.TreeMap D Entry compare) (p : (ByteArray × D) × Nat) =>
        (m.insert (founderId X o p.2) (.live (founderMember X p.1))).insert
          (founderGrantId X o p.2) (.live (founderRoot X (founderId X o p.2)))) m) := by
    intro l
    induction l with
    | nil => intro m hm; exact hm
    | cons p rest ih =>
        intro m hm
        apply ih
        intro id cell hg hk
        rw [Std.TreeMap.getElem?_insert] at hg
        split at hg
        · rename_i he
          have := Std.LawfulEqCmp.eq_of_compare he
          simp only [Option.some.injEq, Entry.live.injEq] at hg
          subst hg
          refine ⟨rfl, by rw [founderRoot_target]; rfl, fun _ => .inr ⟨p.2, this.symm⟩⟩
        · rw [Std.TreeMap.getElem?_insert] at hg
          split at hg
          · simp only [Option.some.injEq, Entry.live.injEq] at hg
            subst hg
            simp [founderMember, kindMember, kindGrant] at hk
          · exact hm id cell hg hk
  have hP := step founders.zipIdx {} (by intro id cell hg; simp at hg)
  intro id cell hl hk
  unfold World.live at hl
  split at hl
  · rename_i hh
    simp only [Option.some.injEq] at hl
    subst hl
    exact hP id _ hh hk
  · simp at hl

end Genesis

omit [Ord D] [DecidableEq D] in
theorem readKind_ok {look : Pinned D} {g : D} {k : Nat} {cell : Cell}
    (h : readKind look g k = .ok cell) : look g = .ok (some cell) ∧ cell.kind = k := by
  unfold readKind at h
  split at h
  · simp at h
  · simp at h
  · rename_i c hc
    split at h
    · simp only [Except.ok.injEq] at h; subst h; exact ⟨hc, by assumption⟩
    · simp at h

omit [Ord D] [DecidableEq D] in
theorem slotDigest_ok {X : Ctx D} {id : D} {cell : Cell} {key : Nat} {d : D}
    (h : slotDigest X id cell key = .ok d) : ∃ b, cell.slots.get key = some b ∧ X.digestOf b = some d := by
  unfold slotDigest at h
  split at h
  · rename_i d' hd
    simp only [Except.ok.injEq] at h
    subst h
    cases hb : cell.slots.get key with
    | none => rw [hb] at hd; simp at hd
    | some b => rw [hb] at hd; exact ⟨b, rfl, hd⟩
  · simp at h

/-- **A World right is a founder's.** Through a rooted World, a grant chain for a right on the World
ends at a live root grant in `R` whose issuer is the chain's principal (with `genesis_rooted` and
`audit_rooted`: a founder's genesis grant, issued by that founder).
Needs the digest decoder to be canonical (a slot read back as a digest IS that digest's bytes). -/
theorem chain_rooted {X : Ctx D} {R : D → Prop} {w : World D} {look : Pinned D}
    (hw : WorldRooted X R w) (hlook : ∀ c v, look c = .ok v → v = w.live c)
    (hdig : ∀ b d, X.digestOf b = some d → b = X.env.bytes d) {right : Right} :
    ∀ {pub : Bool} {g agent p : D}, Chain X look (worldId X) right pub g agent p →
      ∃ r cell, R r ∧ w.live r = some cell ∧ slotDigest X r cell grantIssuer = .ok p
  | _, _, _, _, .root (g := g) hc ht _ _ hi hp => by
      obtain ⟨hlk, hk⟩ := readKind_ok hc
      obtain ⟨b, hb, hd⟩ := slotDigest_ok ht
      have hl := (hlook _ _ hlk).symm
      obtain ⟨_, _, h3⟩ := hw g _ hl hk
      rw [hdig _ _ hd] at hb
      rcases h3 hb with hp' | hr
      · rw [hp] at hp'; simp at hp'
      · exact ⟨g, _, hr, hl, hi⟩
  | _, _, _, _, .link _ _ _ _ _ _ _ rest => chain_rooted hw hlook hdig rest

end Nanodregg.Kernel.Receive
