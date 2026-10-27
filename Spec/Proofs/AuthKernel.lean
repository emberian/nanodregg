/-
# Spec.Proofs.AuthKernel — where every effect of a signed call's walk comes from, by receiver

A kernel lemma proved under Spec for B1 (`Spec.Proofs.Auth`), stated over the kernel's own
definitions only so that KERNEL can move it down beside `Kernel.Proofs.InvokeTree` (it generalises
that module's private `dispatched_effects`/`dispatch_other`, which record only "read as a kind other
than an object's", to what each receiver wrote and on whose authority).

* `effect_prov`: every effect of the signed call's walk is an effect of ONE receiver the walk
  dispatched (`Dispatched`), whose body is the signed one (with the signer as actor) or callable, or
  is the own state write of a dispatched invoke at the object it invoked.
* `node_effect`: one receiver's effect, by the kind it read the cell as: an object (`write`, `law`);
  a member (the signed `rotate` of the signer's own cell, to the key whose digest the cell
  precommitted); a grant (its issuer's retirement, or one append to a counted ledger by an actor
  holding it, `granteeHolds`); an account (a transfer leg or a credit leg, under the source's or the
  well's owner authority, `AccountMove`).
* `changed_effect`: a derived and admitted Turn that changes a live cell carries an effect there,
  the one its touch acts with.
-/
import Kernel.Proofs.InvokeTree
import Kernel.Proofs.LedgerNext
import Kernel.Proofs.Ledger

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The vocabulary -/

/-- `actor` exercises `owner`'s authority over `obj` for `right`: it is the owner, acting with no
grant, or it holds a grant chain from `via`, every link pinned, live, aimed at `obj` and carrying
`right`, whose root issuer is `owner` (`Chain`). -/
def Exercises (X : Ctx D) (look : Pinned D) (obj : D) (right : Right) (via : Option D) (actor owner : D) :
    Prop :=
  via = none ∧ actor = owner ∨ ∃ g, via = some g ∧ Chain X look obj right true g actor owner

/-- A receiver `b`, run as `a`, moves the account `id`: it is a transfer and `id` is its source or
its destination, under the source owner's `transfer` authority; or a credit line and `id` is the
well or the credited account, under the well owner's `credit` authority. -/
def AccountMove (X : Ctx D) (look : Pinned D) (a : D) (b : Body D) (id : D) : Prop :=
  (∃ srcR dstR amount via once scell owner, b = .transfer srcR dstR amount via once ∧
      (id = srcR.resolve X ∨ id = dstR.resolve X) ∧ readKind look (srcR.resolve X) kindAccount = .ok scell ∧
      slotDigest X (srcR.resolve X) scell slotOwner = .ok owner ∧
      Exercises X look (srcR.resolve X) (.transfer 0) via a owner) ∨
  (∃ well acctR amount via wcell owner, b = .credit well acctR amount via ∧
      (id = well ∨ id = acctR.resolve X) ∧ readKind look well kindAccount = .ok wcell ∧
      slotDigest X well wcell slotOwner = .ok owner ∧ Exercises X look well (.credit 0) via a owner)

/-- **One receiver's effect `e`** (receiver `b`, run as `a`, on the view `look`), by the kind it read
the cell as: an object; the signer's own member cell under its `rotate` to the precommitted key; a
grant retired by its issuer or appended by an actor holding it; an account moved (`AccountMove`). -/
def NodeEffect (X : Ctx D) (look : Pinned D) (c : Call D) (a : D) (b : Body D) (e : D × Act) : Prop :=
  (∃ cl, readKind look e.1 kindObject = .ok cl) ∨
  (∃ key next m, b = .rotate key next ∧ e.1 = c.unsigned.member ∧ readKind look e.1 kindMember = .ok m ∧
      c.unsigned.key = key ∧ slotDigest X e.1 m slotNext = .ok (nextKeyDigest X key)) ∨
  (∃ cl, readKind look e.1 kindGrant = .ok cl ∧
      (e.2 = .retire ∧ slotDigest X e.1 cl grantIssuer = .ok a ∨
        LedgerSpend e.1 cl e.2 ∧ granteeHolds X look e.1 cl a true = .ok ())) ∨
  (∃ cl, readKind look e.1 kindAccount = .ok cl ∧
      (AccountMove X look a b e.1 ∨ e.2 = .retire ∧ slotDigest X e.1 cl slotOwner = .ok a)) ∨
  (∃ i key next cl au, b = .rotateCertifier i key next ∧ e.1 = c.unsigned.member ∧
      readKind look e.1 kindAuthority = .ok cl ∧ authorityOfCell cl = some au ∧ c.unsigned.key = key ∧
      au.preRotated X i key = true ∧ e.2 = .write (rotationOps X i key next))

/-- **Where an effect of `c`'s walk on `w` comes from**: a receiver the walk dispatched (the signed
body as the signer, or a callable body), and either that receiver, if not an invoke, derived it, or
it is the own write of a dispatched invoke at the object the invoke ran on. -/
def Prov (X : Ctx D) (w : World D) (c : Call D) (e : D × Act) : Prop :=
  ∃ n wk a ca b, Dispatched X w c n wk a ca b ∧ (b = c.unsigned.body ∧ a = c.unsigned.member ∨ b.callable = true) ∧
    ((∃ r, b.isInvoke = false ∧ dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a ca b = .ok r ∧
        e ∈ r.1.effects) ∨
     ∃ obj method args budget via cell p rq, b = .invoke obj method args budget via ∧ e.1 = obj ∧
       invokeRun X (pinned X.env w c.unsigned.pins) c a ca obj method via = .ok (cell, p, rq))

/-! ## Small facts -/

omit [Ord D] in
/-- What a passing owner check means: the owner slot reads, and the actor exercises its authority. -/
theorem ownerAuthority_exercises {X : Ctx D} {look : Pinned D} {actor obj : D} {cell : Cell} {right : Right}
    {via : Option D} {principal : D} (h : ownerAuthority X look actor obj cell right via = .ok principal) :
    ∃ owner, slotDigest X obj cell slotOwner = .ok owner ∧ Exercises X look obj right via actor owner := by
  unfold ownerAuthority at h
  simp only [except_bind_ok] at h
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, -⟩ := h
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨p, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g => right; exact ⟨g, rfl, walk_chain hp⟩

omit [Ord D] in
/-- An invoke's run is handed only past the owner check, on the cell it read. -/
theorem invokeRun_authority {X : Ctx D} {look : Pinned D} {c : Call D} {actor obj : D} {caller : Option D} {method : Nat}
    {via : Option D} {cell : Cell} {p : D} {r : Req D}
    (h : invokeRun X look c actor caller obj method via = .ok (cell, p, r)) :
    ∃ principal, ownerAuthority X look actor obj cell (.invoke method) via = .ok principal := by
  unfold invokeRun at h
  simp only [except_bind_ok] at h
  obtain ⟨cell', -, pkg, -, p', -, principal, ha, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, -⟩ := h
  exact ⟨principal, ha⟩

omit [Ord D] in
/-- An invoke reads its object as an object. -/
theorem invokeRun_readKind {X : Ctx D} {look : Pinned D} {c : Call D} {actor obj : D} {caller : Option D} {method : Nat}
    {via : Option D} {cell : Cell} {p : D} {r : Req D}
    (h : invokeRun X look c actor caller obj method via = .ok (cell, p, r)) : readKind look obj kindObject = .ok cell := by
  unfold invokeRun at h
  simp only [except_bind_ok] at h
  obtain ⟨cell', hk, pkg, -, p', -, principal, -, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, -⟩ := h
  exact hk

/-- A pinned read of a kind reads the live cell, and the cell is of that kind. -/
theorem readKind_live {E : Env D} {w : World D} {pins : List (D × D)} {x : D} {k : Nat} {cl cell : Cell}
    (h : readKind (pinned E w pins) x k = .ok cl) (hl : w.live E x = some cell) : cl = cell ∧ cell.kind = k := by
  have h1 := (readKind_pinned h).1
  rw [hl] at h1
  cases h1
  refine ⟨rfl, ?_⟩
  unfold readKind at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h; assumption
    · cases h

omit [Ord D] in
/-- A chain's first link is a grant the agent holds. -/
theorem chain_holds {X : Ctx D} {look : Pinned D} {obj : D} {right : Right} {pub : Bool} {g agent p : D}
    (h : Chain X look obj right pub g agent p) :
    ∃ cell, readKind look g kindGrant = .ok cell ∧ granteeHolds X look g cell agent pub = .ok () := by
  cases h with
  | root hc _ hg => exact ⟨_, hc, hg⟩
  | link hc _ hg => exact ⟨_, hc, hg⟩

omit [Ord D] in
private theorem spend_node {X : Ctx D} {look : Pinned D} {c : Call D} {a : D} {b : Body D} {base : Nat}
    {g : D} {cell : Cell} {units : Nat} {short : Refusal D} {ef : Option (D × Act)} (hb : LedgerBase base)
    (hg : readKind look g kindGrant = .ok cell) (hh : granteeHolds X look g cell a true = .ok ())
    (h : spendAt base g cell units short = .ok ef) : ∀ e ∈ ef.toList, NodeEffect X look c a b e := by
  obtain ⟨i, left, hl, hu, hc⟩ := spendAt_ok h
  rcases hc with ⟨-, rfl⟩ | ⟨h0, hi, rfl⟩
  · simp
  · intro e he
    simp only [Option.toList_some, List.mem_singleton] at he
    subst he
    exact .inr (.inr (.inl ⟨cell, hg, .inr ⟨⟨base, i, left, units, hb, hl, Nat.pos_of_ne_zero h0, hu, hi, rfl⟩, hh⟩⟩))

omit [Ord D] in
private theorem carve_node {X : Ctx D} {look : Pinned D} {c : Call D} {a : D} {b : Body D} {target : D}
    {rights : List Right} {parent : Option D} {ef : Option (D × Act)}
    (h : checkParent X look a target rights parent = .ok ef) : ∀ e ∈ ef.toList, NodeEffect X look c a b e := by
  cases parent with
  | none =>
      simp only [checkParent, except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨⟨⟩, -, rfl⟩ := h
      simp
  | some p =>
      simp only [checkParent, except_bind_ok] at h
      obtain ⟨pc, hpc, pt, -, ⟨⟩, -, pg, hpg, ⟨⟩, hpe, ⟨⟩, -, h⟩ := h
      rw [req_ok, decide_eq_true_eq] at hpe
      rw [hpe] at hpg
      have hh : granteeHolds X look p pc a true = .ok () := by
        unfold granteeHolds
        rw [hpg]
        simp [bind, Except.bind, pure, Except.pure]
      intro e he
      split at h
      · exact spend_node (.inl rfl) hpc hh h e he
      · split at h
        · exact spend_node (.inr (.inl rfl)) hpc hh h e he
        · split at h
          · exact spend_node (.inr (.inr rfl)) hpc hh h e he
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h; simp at he

omit [Ord D] in
/-- A spend through `via` by an actor exercising authority through `via`'s chain is an append by a
holder of the grant. -/
private theorem spendVia_node {X : Ctx D} {look : Pinned D} {c : Call D} {a : D} {b : Body D} {base : Nat}
    {via : Option D} {units : Nat} {short : D → Refusal D} {ef : Option (D × Act)} {obj : D} {right : Right}
    {owner : D} (hb : LedgerBase base) (hx : Exercises X look obj right via a owner)
    (h : spendVia look base via units short = .ok ef) : ∀ e ∈ ef.toList, NodeEffect X look c a b e := by
  rcases spendVia_ok h with ⟨-, rfl⟩ | ⟨g, gc, rfl, hgc, hsa⟩
  · simp
  · rcases hx with ⟨h0, -⟩ | ⟨g', hg', hch⟩
    · cases h0
    · cases hg'
      obtain ⟨cl, hcl, hh⟩ := chain_holds hch
      rw [hgc] at hcl
      cases hcl
      exact spend_node hb hgc hh hsa

/-! ## One receiver -/

omit [Ord D] in
/-- **What one receiver other than an invoke writes**, by the kind it read each cell as. -/
theorem node_effect {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Receive.Sub D}
    {wk : Walk D} {a : D} {ca : Option D} {b : Body D} {r : Draft D × Walk D}
    (hi : b.isInvoke = false) (h : dispatch X look rv c sub wk a ca b = .ok r) :
    ∀ e ∈ r.1.effects, NodeEffect X look c a b e := by
  cases b with
  | invoke => simp [Body.isInvoke] at hi
  | write o ed v =>
      intro e he
      obtain ⟨cl, _, _, hko, -, -, -, -, hdeq⟩ := write_judged (stepped_draft h)
      rw [hdeq] at he
      simp only [writeOf, List.mem_singleton] at he
      subst he
      exact .inl ⟨cl, hko⟩
  | law o ls v =>
      intro e he
      obtain ⟨cl, _, _, hko, -, -, -, -, -, -, hef⟩ := law_judged (stepped_draft h)
      rw [hef] at he
      simp only [writeOf, List.mem_singleton] at he
      subst he
      exact .inl ⟨cl, hko⟩
  | createOf pkg laws state =>
      intro e he
      rw [(createOf_parts (stepped_draft h)).1] at he
      simp at he
  | enroll key next possession via =>
      have hd := stepped_draft h
      unfold enroll at hd
      simp only [except_bind_ok] at hd
      obtain ⟨p, hw, g, hg, spend, hs, ⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      obtain ⟨cl, hcl, hh⟩ := chain_holds (walk_chain hw)
      rw [hg] at hcl
      cases hcl
      exact spend_node (.inl rfl) hg hh hs e he
  | rotate key next =>
      have hd := stepped_draft h
      unfold rotate at hd
      simp only [except_bind_ok] at hd
      obtain ⟨m, hm, ⟨⟩, hk, cm, hcm, ⟨⟩, hn, hd⟩ := hd
      rw [req_ok, decide_eq_true_eq] at hk hn
      rw [hn] at hcm
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      simp only [List.mem_singleton] at he
      subst he
      exact .inr (.inl ⟨key, next, m, rfl, rfl, hm, hk, hcm⟩)
  | rotateCertifier i key next =>
      obtain ⟨cl, au, hka, hdec, hkey, hpre, hd⟩ := rotateCertifier_ok (stepped_draft h)
      intro e he
      rw [hd] at he
      simp only [List.mem_singleton] at he
      subst he
      exact .inr (.inr (.inr (.inr ⟨i, key, next, cl, au, rfl, rfl, hka, hdec, hkey, hpre, rfl⟩)))
  | install pkg =>
      have hd := stepped_draft h
      unfold install at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he; rw [← hd] at he; simp at he
  | create pkg laws state =>
      have hd := stepped_draft h
      unfold create at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hd⟩ := hd
      intro e he
      cases pkg with
      | none =>
          simp only [bind, Except.bind, pure, Except.pure] at hd
          injection hd with hd
          rw [← hd] at he; simp at he
      | some p =>
          simp only [except_bind_ok] at hd
          obtain ⟨_, -, hd⟩ := hd
          simp only [pure, Except.pure] at hd
          injection hd with hd
          rw [← hd] at he; simp at he
  | grant target grantee rights parent =>
      have hd := stepped_draft h
      unfold grant at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, ⟨⟩, -, carve, hcv, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      exact carve_node hcv e he
  | retire x =>
      have hd := stepped_draft h
      unfold retire at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, hchk, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      simp only [List.mem_singleton] at he
      subst he
      cases hl : look x with
      | error err =>
          simp only [retireCheck, hl] at hchk
          obtain ⟨_, h1, -⟩ := except_bind_ok.mp hchk; cases h1
      | ok o =>
      cases o with
      | none =>
          simp only [retireCheck, hl] at hchk
          obtain ⟨_, h1, -⟩ := except_bind_ok.mp hchk; cases h1
      | some cell =>
      simp only [retireCheck, hl] at hchk
      obtain ⟨cl, hcl, hchk⟩ := except_bind_ok.mp hchk
      simp only [Except.ok.injEq] at hcl
      subst hcl
      have hrk : ∀ k, cell.kind = k → readKind look x k = .ok cell := fun k hk => by
        simp [readKind, hl, hk]
      by_cases hg : cell.kind = kindGrant
      · rw [if_pos hg] at hchk
        simp only [except_bind_ok] at hchk
        obtain ⟨issuer, hiss, hie⟩ := hchk
        rw [req_ok, decide_eq_true_eq] at hie
        rw [hie] at hiss
        exact .inr (.inr (.inl ⟨cell, hrk _ hg, .inl ⟨rfl, hiss⟩⟩))
      rw [if_neg hg] at hchk
      by_cases ho : cell.kind = kindObject
      · exact .inl ⟨cell, hrk _ ho⟩
      rw [if_neg ho] at hchk
      by_cases ha : cell.kind = kindAccount
      · rw [if_pos ha] at hchk
        simp only [except_bind_ok] at hchk
        obtain ⟨owner, hown, ⟨⟩, hoe, -⟩ := hchk
        rw [req_ok, decide_eq_true_eq] at hoe
        rw [hoe] at hown
        exact .inr (.inr (.inr (.inl ⟨cell, hrk _ ha, .inr ⟨rfl, hown⟩⟩)))
      rw [if_neg ha] at hchk
      cases hchk
  | issue cap =>
      have hd := stepped_draft h
      unfold issue at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he; rw [← hd] at he; simp at he
  | account asset owner =>
      have hd := stepped_draft h
      simp only [account, pure, Except.pure, Except.ok.injEq] at hd
      intro e he; rw [← hd] at he; simp at he
  | transfer srcR dstR amount via once =>
      intro e he
      obtain ⟨scell, sv, dcell, dv, principal, spend, hs, hdr, hau, -, -, -, -, -, hsp, hd⟩ :=
        transfer_ok (stepped_draft h)
      obtain ⟨owner, ho, hx⟩ := ownerAuthority_exercises hau
      have hks : readKind look (srcR.resolve X) kindAccount = .ok scell := (readAccount_ok (readRef_ok hs).2.1).1
      have hkd : readKind look (dstR.resolve X) kindAccount = .ok dcell := (readAccount_ok (readRef_ok hdr).2.1).1
      have hmove : ∀ id, (id = srcR.resolve X ∨ id = dstR.resolve X) →
          AccountMove X look a (.transfer srcR dstR amount via once) id :=
        fun id hid => .inl ⟨srcR, dstR, amount, via, once, scell, owner, rfl, hid, hks, ho, hx⟩
      rw [hd] at he
      simp only [List.cons_append, List.nil_append, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact .inr (.inr (.inr (.inl ⟨scell, hks, .inl (hmove _ (.inl rfl))⟩)))
      · exact .inr (.inr (.inr (.inl ⟨dcell, hkd, .inl (hmove _ (.inr rfl))⟩)))
      · exact spendVia_node (.inr (.inl rfl)) hx hsp e he
  | credit well acctR amount via =>
      intro e he
      obtain ⟨wcell, wv, acell, av, principal, spend, hs, hda, hau, -, -, -, -, -, -, hsp, hd⟩ :=
        credit_ok (stepped_draft h)
      obtain ⟨owner, ho, hx⟩ := ownerAuthority_exercises hau
      have hkw : readKind look well kindAccount = .ok wcell := (readAccount_ok hs).1
      have hka : readKind look (acctR.resolve X) kindAccount = .ok acell := (readAccount_ok (readRef_ok hda).2.1).1
      have hmove : ∀ id, (id = well ∨ id = acctR.resolve X) → AccountMove X look a (.credit well acctR amount via) id :=
        fun id hid => .inr ⟨well, acctR, amount, via, wcell, owner, rfl, hid, hkw, ho, hx⟩
      rw [hd] at he
      simp only [List.cons_append, List.nil_append, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact .inr (.inr (.inr (.inl ⟨wcell, hkw, .inl (hmove _ (.inl rfl))⟩)))
      · exact .inr (.inr (.inr (.inl ⟨acell, hka, .inl (hmove _ (.inr rfl))⟩)))
      · exact spendVia_node (.inr (.inr rfl)) hx hsp e he

/-! ## The walk -/

omit [Ord D] [DecidableEq D] in
private theorem foldCalls_succ' {sub : Receive.Sub D} {obj : D} {calls : List (Body D)} {i : Nat}
    (hi : i < calls.length) {a0 acc q : Draft D × Walk D}
    (hpre : (calls.take i).foldlM (callStep sub obj) a0 = .ok acc) (hq : callStep sub obj acc calls[i] = .ok q) :
    (calls.take (i + 1)).foldlM (callStep sub obj) a0 = .ok q := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldlM_append, hpre]
  simp [bind, Except.bind, hq, pure, Except.pure]

private theorem walk_prov_step {X : Ctx D} {w : World D} {c : Call D} (n : Nat)
    (ihP : ∀ m, n = m + 1 → ∀ {wk : Walk D} {a : D} {ca : Option D} {b : Body D} {r : Draft D × Walk D},
      Dispatched X w c m wk a ca b → b.callable = true →
      dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c m) wk a ca b = .ok r →
      ∀ e ∈ r.1.effects, Prov X w c e)
    {wk : Walk D} {a : D} {ca : Option D} {b : Body D} {r : Draft D × Walk D} (hd : Dispatched X w c n wk a ca b)
    (hroot : b = c.unsigned.body ∧ a = c.unsigned.member ∨ b.callable = true)
    (h : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a ca b = .ok r) :
    ∀ e ∈ r.1.effects, Prov X w c e := by
  cases hb : b.isInvoke with
  | false => exact fun e he => ⟨n, wk, a, ca, b, hd, hroot, .inl ⟨r, hb, h, he⟩⟩
  | true =>
  cases b with
  | invoke obj method args budget via =>
      have hok := h
      simp only [dispatch] at hok
      obtain ⟨-, cell, p, rq, new, calls, rows, used, hir, hrun, -, -, -, -, -, hdc⟩ := invoke_ok hok
      unfold deriveCalls at hdc
      have key : ∀ (suf : List (Body D)) (i : Nat) (acc r' : Draft D × Walk D),
          suf = calls.drop i →
          (calls.take i).foldlM (callStep (tree X (pinned X.env w c.unsigned.pins)
            (rowView X.env w c.unsigned) c n) obj)
            (⟨[], writeOf obj (diffOps (stateOf cell) new), [], rows⟩,
              { wk with visited := obj :: wk.visited, pool := wk.pool - used }) = .ok acc →
          suf.foldlM (callStep (tree X (pinned X.env w c.unsigned.pins)
            (rowView X.env w c.unsigned) c n) obj) acc = .ok r' →
          (∀ e ∈ acc.1.effects, Prov X w c e) → ∀ e ∈ r'.1.effects, Prov X w c e := by
        intro suf
        induction suf with
        | nil =>
            intro i acc r' _ _ hf ha
            simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
            subst hf
            exact ha
        | cons b rest ihs =>
            intro i acc r' hsuf hpre hf ha
            have hi : i < calls.length := by
              rcases Nat.lt_or_ge i calls.length with h | h
              · exact h
              · rw [List.drop_eq_nil_of_le h] at hsuf
                cases hsuf
            have hsuf' := hsuf
            rw [← List.getElem_cons_drop hi] at hsuf'
            have hb : calls[i] = b := (List.cons.inj hsuf').1.symm
            have hrest : rest = calls.drop (i + 1) := (List.cons.inj hsuf').2
            rw [List.foldlM_cons, except_bind_ok] at hf
            obtain ⟨q', hq', hf⟩ := hf
            have hpre' := foldCalls_succ' hi hpre (by rw [hb]; exact hq')
            obtain ⟨q, hq, rfl⟩ := callStep_ok hq'
            obtain ⟨m', hm, hcall, hq2⟩ := effect_as_signed hq
            have hchild : Dispatched X w c m' acc.2 obj (some obj) b := by
              subst hm
              rw [← hb]
              exact Dispatched.call i hi hd hok hir hrun hpre
            have hq3 := ihP m' hm hchild hcall hq2
            refine ihs (i + 1) _ r' hrest hpre' hf (fun e he => ?_)
            simp only [Draft.append, List.mem_append] at he
            rcases he with he | he
            · exact ha e he
            · exact hq3 e he
      refine key calls 0 _ r rfl rfl hdc (fun e he => ?_)
      simp only [writeOf, List.mem_singleton] at he
      subst he
      exact ⟨n, wk, a, ca, _, hd, hroot, .inr ⟨obj, method, args, budget, via, cell, p, rq, rfl, rfl, hir⟩⟩
  | _ => simp [Body.isInvoke] at hb

private theorem walk_prov {X : Ctx D} {w : World D} {c : Call D} :
    ∀ n {wk : Walk D} {a : D} {ca : Option D} {b : Body D} {r : Draft D × Walk D}, Dispatched X w c n wk a ca b →
      (b = c.unsigned.body ∧ a = c.unsigned.member ∨ b.callable = true) →
      dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a ca b = .ok r →
      ∀ e ∈ r.1.effects, Prov X w c e := by
  intro n
  induction n with
  | zero => exact fun hd hr h => walk_prov_step 0 (fun _ h => absurd h (by omega)) hd hr h
  | succ m ih =>
      exact fun hd hr h => walk_prov_step (m + 1) (fun m' hm => by
        obtain rfl : m' = m := by omega
        intro wk' a' ca' b' r' hd' hc h'
        exact ih hd' (.inr hc) h') hd hr h

/-- **Every effect of the signed call's walk has a provenance** (`Prov`): one receiver the walk
dispatched derived it, or it is a dispatched invoke's own write at its object. -/
theorem effect_prov {X : Ctx D} {w : World D} {c : Call D} {R : Draft D × Walk D}
    (hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member none c.unsigned.body = .ok R)
    {e : D × Act} (he : e ∈ R.1.effects) : Prov X w c e :=
  walk_prov _ .root (.inl ⟨rfl, rfl⟩) hR e he

/-! ## At the World -/

/-- **A Turn that changes a live cell carries an effect there**: a signed call derived from `w` and
admitted to `w'`, and a cell live in `w` whose entry in `w'` differs: the call's walk has an effect
at the cell, and the Turn's touch of the cell acts with it. -/
theorem changed_effect {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {id : D} {cell : Cell}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') (hl : w.live X.env id = some cell)
    (hne : w'.live X.env id ≠ some cell) :
    ∃ R e, dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
        ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member none c.unsigned.body = .ok R ∧
      e ∈ R.1.effects ∧ e.1 = id ∧ ∃ x ∈ t.touches, x.cell = id ∧ x.act = e.2 := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, _k, hd, hs⟩ := receiveWith_sealed hw
  replace hd := derive_of_withTicks hd
  rw [derive_eq] at hd
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member none c.unsigned.body with
  | error e => rw [hR] at hd; cases hd
  | ok R =>
  rw [hR] at hd
  simp only [Except.map, Except.ok.injEq] at hd
  subst hd
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  obtain ⟨posts, hck, -⟩ := admit_ok ha
  cases hf : R.1.effects.find? (fun e => decide (e.1 = id)) with
  | none =>
      refine absurd ?_ hne
      have hframe := admit_frame (c := id) ha (fun x hx hxc => by
        rw [htouch] at hx
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
        simp only at hxc ⊢
        rw [hxc]; unfold actFor; rw [hf]) (live_not_created hck hl)
      unfold World.live; rw [hframe]; exact hl
  | some e =>
      have he := List.mem_of_find?_eq_some hf
      have heg : e.1 = id := by simpa using List.find?_some hf
      obtain ⟨q, hq, hqe⟩ := hpins e he
      have hact : actFor R.1.effects id = e.2 := by unfold actFor; rw [hf]
      have hx : ({ cell := q.1, seen := q.2, act := actFor R.1.effects q.1 } : Touch D) ∈ t.touches := by
        rw [htouch]; exact List.mem_map_of_mem hq
      refine ⟨R, e, by first | exact hR | rfl, he, heg, _, hx, hqe.trans heg, ?_⟩
      show actFor R.1.effects q.1 = e.2
      rw [hqe, heg, hact]

end Nanodregg.Spec
