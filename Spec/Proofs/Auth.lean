/-
# Spec.Proofs.Auth — B1, authority confinement (TOPLEVEL-SPEC §3.1), for every cell

seL4's integrity (Sewell et al. 2011) in the kernel's terms. **The claim** (`Integrity.authority`):
along an audited log from a World whose cells are canonical, every step that changes a cell live at
the World it is taken from is a Turn the system derived from the signed call its event decodes to,
and that call was entitled to the change (`Authorized`, at the World it was derived against):

* an object: its owner's `write`/`law` (directly, or through a grant chain rooted at the owner
  carrying `mutate`), or an invoke the call's walk dispatched whose actor exercises the owner's
  `invoke method` authority;
* a member: only the signer's own `rotate`, to the key whose digest the cell precommitted, signed by
  that key;
* a grant: its retirement by its issuer, or ONE append to one counted ledger by an actor holding it;
* a value account: a transfer leg or a credit leg, under the source owner's `transfer` (or the well
  owner's `credit`) authority, exercised by the dispatched actor;
* a ROM cell (a package, the authority cell): never.

A refusal changes no cell. A cell born inside the log is covered from its birth on (the claim
quantifies over every step, at the cell live at that step's World); the birth itself is not a
change of a live cell.

**Premises.** `Audited` (each step is the system's own decision: without it a step has no call to be
authorized); `CellsCanon` at the start (the `write` arm reads its cell's slots in canonical order;
genesis has it, `genesis_cellsCanon`, and every admitted Turn keeps it). Both hold of the deployed
system.

**Lemmas.** `Spec.Proofs.AuthKernel` (a kernel lemma proved here, for KERNEL to move down:
`effect_prov`, `node_effect`, `changed_effect`), `object_turn_cases`, `write_next_slots`,
`law_next_slots`, `invoke_tree_slots`, `admit_rom`, `admit_retired`, `admit_written`.

**Floor.** `openKernel` (`Spec.Sim.Auth`): `write` without the owner check. Founder 1 of a two-founder
genesis writes founder 0's object; it derives, admits, and changes the cell, and no arm holds.

**Owed.** The arms name the authority at the receiver the walk dispatched; for a nested receiver
(an object's run) that actor is the calling object, whose own invoke is in turn authorized (its
`objectInvoke` step). A claim that chains every nested actor back to the signer is not stated here.
-/
import Spec.Proofs.AuthKernel
import Spec.Proofs.Bridge
import Spec.Sim.Auth
import Kernel.Proofs.Logic.History
import Kernel.Proofs.Frame
import Kernel.Proofs.Rederive
import Codec.Proofs.Digest

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The claim -/

/-- **A step of a log, at the World it is taken from**: `StepAt S w l v s v'` says the system's
kernel, folding `l` from `w`, reaches `v`, takes step `s` there and reaches `v'`. -/
inductive StepAt (S : System D) : World D → List (Step D) → World D → Step D → World D → Prop
  | here {w w' : World D} {s : Step D} {rest : List (Step D)} :
      S.step w s = .ok w' → StepAt S w (s :: rest) w s w'
  | later {w w₁ v v' : World D} {s s' : Step D} {rest : List (Step D)} :
      S.step w s = .ok w₁ → StepAt S w₁ rest v s' v' → StepAt S w (s :: rest) v s' v'

/-- **What the signed call `c`, derived against `w`, was entitled to do to cell `id`** (live as `cell`
at `w`; `after` its entry once the Turn is admitted). One arm per change the kernel may make; a ROM
cell has none. Authority is read through the call's pins (`pinned`), at the receiver the call's walk
dispatched (`Dispatched`: the signed body as the signer, or a nested receiver as the object whose run
returned it). -/
inductive Authorized (X : Ctx D) (w : World D) (c : Call D) (id : D) (cell : Cell) : Option Cell → Prop
  | objectWrite {after : Option Cell} {edits : List (Nat × Option ByteArray)} {via : Option D} {owner : D} :
      cell.kind = kindObject → c.unsigned.body = .write id edits via →
      slotDigest X id cell slotOwner = .ok owner →
      Exercises X (pinned X.env w c.unsigned.pins) id .mutate via c.unsigned.member owner →
      Authorized X w c id cell after
  | objectLaw {after : Option Cell} {laws : List D} {via : Option D} {owner : D} :
      cell.kind = kindObject → c.unsigned.body = .law id laws via →
      slotDigest X id cell slotOwner = .ok owner →
      Exercises X (pinned X.env w c.unsigned.pins) id .mutate via c.unsigned.member owner →
      Authorized X w c id cell after
  | objectInvoke {after : Option Cell} {n : Nat} {wk : Walk D} {actor : D} {method : Nat} {args : ByteArray}
      {budget : Nat} {via : Option D} {owner : D} :
      cell.kind = kindObject → Dispatched X w c n wk actor (.invoke id method args budget via) →
      slotDigest X id cell slotOwner = .ok owner →
      Exercises X (pinned X.env w c.unsigned.pins) id (.invoke method) via actor owner →
      Authorized X w c id cell after
  | member {after : Option Cell} {key : ByteArray} {next : D} :
      cell.kind = kindMember → c.unsigned.body = .rotate key next → id = c.unsigned.member →
      c.unsigned.key = key → slotDigest X id cell slotNext = .ok (nextKeyDigest X key) →
      X.verify key (X.callMessage c.unsigned) c.signature = true →
      Authorized X w c id cell after
  | grantRetired {n : Nat} {wk : Walk D} {actor : D} {b : Body D} :
      cell.kind = kindGrant → Dispatched X w c n wk actor b →
      slotDigest X id cell grantIssuer = .ok actor → Authorized X w c id cell none
  | grantSpent {n : Nat} {wk : Walk D} {actor : D} {b : Body D} {base i left u : Nat} :
      cell.kind = kindGrant → Dispatched X w c n wk actor b →
      granteeHolds X (pinned X.env w c.unsigned.pins) id cell actor true = .ok () →
      LedgerBase base → ledgerLeft base id cell = .ok (i, left) → 0 < u → u ≤ left → i ≤ ledgerSpendsMax →
      Authorized X w c id cell (some { cell with slots := cell.slots.set (base + i) (countBytes (left - u)) })
  | account {after : Option Cell} {n : Nat} {wk : Walk D} {actor : D} {b : Body D} :
      cell.kind = kindAccount → Dispatched X w c n wk actor b →
      AccountMove X (pinned X.env w c.unsigned.pins) actor b id → Authorized X w c id cell after
  /-- KERNEL-70: the object's owner signed its retirement (every law in force judged it); it ends -/
  | objectRetired :
      cell.kind = kindObject → c.unsigned.body = .retire id →
      slotDigest X id cell slotOwner = .ok c.unsigned.member → Authorized X w c id cell none
  /-- KERNEL-70: the account's owner retired it (it held nothing); it ends -/
  | accountRetired {n : Nat} {wk : Walk D} {actor : D} {b : Body D} :
      cell.kind = kindAccount → Dispatched X w c n wk actor b →
      slotDigest X id cell slotOwner = .ok actor → Authorized X w c id cell none

/-- **B1. Authority confinement.** Along an audited log from a World whose cells are canonical,
every step that changes a cell live at the World it is taken from is a Turn, derived by the
system's `receive` from the signed call its event decodes to, and that call was entitled to the
change (`Authorized`, at the World it was derived against). A refusal never changes a cell. -/
def Integrity.authority (S : System D) : Prop :=
  ∀ {w w' : World D} {l : List (Step D)}, Audited S w l w' → CellsCanon S.X.env w →
    ∀ {v v' : World D} {s : Step D}, StepAt S w l v s v' →
    ∀ {id : D} {cell : Cell}, v.live S.X.env id = some cell → v'.live S.X.env id ≠ some cell →
      ∃ t c, s = .turn t ∧ S.X.decodeCall t.event = some c ∧ S.receive v c = .ok t ∧
        Authorized S.X v c id cell (v'.live S.X.env id)

/-! ## The kernel's step -/

/-- **One derived and admitted Turn changes a live cell only as the call was entitled to.** A ROM
cell is kept (`admit_rom`); an object by `object_turn_cases` and the owner check each of its
receivers passed; any other cell carries an effect of the walk (`changed_effect`) that one
dispatched receiver derived (`effect_prov`), whose kind and authority `node_effect` names. -/
theorem step_authorized [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {id : D} {cell : Cell}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') (hcan : CellsCanon X.env w)
    (hl : w.live X.env id = some cell) (hne : w'.live X.env id ≠ some cell) :
    Authorized X w c id cell (w'.live X.env id) := by
  by_cases hrom : cell.discipline = .rom
  · exact absurd (admit_rom ha hl hrom) hne
  by_cases hk : cell.kind = kindObject
  · rcases object_turn_cases hc ha hl hk with ⟨hkeep, hnc, hnw, hnl, -, hni⟩ | ⟨edits, via, hb⟩ |
        ⟨laws', via, hb⟩ | hb | ⟨n, wk, a, method, args, budget, via, hd⟩
    · exact absurd ((object_step_none (.keep hc ha hkeep hnc hnw hnl hni)).trans hl) hne
    · obtain ⟨principal, laws, -, hau, -⟩ := write_next_slots hc ha hb hl (hcan _ _ hl)
      obtain ⟨owner, ho, hx⟩ := ownerAuthority_exercises hau
      exact .objectWrite hk hb ho hx
    · obtain ⟨principal, laws, -, hau, -⟩ := law_next_slots hc ha hb hl
      obtain ⟨owner, ho, hx⟩ := ownerAuthority_exercises hau
      exact .objectLaw hk hb ho hx
    · obtain ⟨-, -, hown, -, -, -⟩ := retire_next hc hb hl hk
      have hn : w'.live X.env id = none := by unfold World.live; rw [retire_next_tomb hc ha hb]
      rw [hn]
      exact .objectRetired hk hb hown
    · obtain ⟨cell₀, p, r, s, calls, rows, used, laws, hr, -⟩ := invoke_tree_slots hc ha hd
      have hl₀ := invokeRun_live hr
      rw [hl] at hl₀
      cases hl₀
      obtain ⟨principal, hau⟩ := invokeRun_authority hr
      obtain ⟨owner, ho, hx⟩ := ownerAuthority_exercises hau
      exact .objectInvoke hk hd ho hx
  obtain ⟨R, e, hR, he, heid, x, hx, hxc, hxa⟩ := changed_effect hc ha hl hne
  obtain ⟨n, wk, a, b, hd, hroot, hprov⟩ := effect_prov hR he
  have hnode : NodeEffect X (pinned X.env w c.unsigned.pins) c a b e := by
    rcases hprov with ⟨r, hi, hr, her⟩ | ⟨obj, method, args, budget, via, cl, p, rq, -, he1, hir⟩
    · exact node_effect hi hr e her
    · exact .inl ⟨cl, he1 ▸ invokeRun_readKind hir⟩
  obtain ⟨eid, eact⟩ := e
  simp only at heid hxa
  subst heid
  rcases hnode with ⟨cl, hko⟩ | ⟨key, next, m, hb, hm, hkm, hkey, hslot⟩ | ⟨cl, hkg, hret | ⟨hsp, hh⟩⟩ |
      ⟨cl, hka, hmove⟩
  · exact absurd (readKind_live hko hl).2 hk
  · obtain ⟨rfl, hkind⟩ := readKind_live hkm hl
    have hb' : c.unsigned.body = .rotate key next := by
      rcases hroot with ⟨hb0, -⟩ | hcall
      · exact hb0.symm.trans hb
      · rw [hb] at hcall; simp [Body.callable] at hcall
    obtain ⟨-, hw⟩ := receive_ok_with hc
    obtain ⟨hv, -⟩ := receiveWith_sealed hw
    rw [hkey] at hv
    exact .member hkind hb' hm hkey hslot hv
  · obtain ⟨rfl, hkind⟩ := readKind_live hkg hl
    have hnone := admit_retired ha hx (hxa.trans hret.1)
    rw [hxc] at hnone
    rw [hnone]
    exact .grantRetired hkind hd hret.2
  · obtain ⟨rfl, hkind⟩ := readKind_live hkg hl
    obtain ⟨base, i, left, u, hbase, hll, hu0, hu, hi, hw⟩ := hsp
    obtain ⟨cell1, post, hc1, hp, hl'⟩ := admit_written ha hx (hxa.trans hw)
    rw [hxc] at hc1 hl'
    rw [hl] at hc1
    cases hc1
    rw [hl', postWrite_eq hp]
    exact .grantSpent hkind hd hh hbase hll hu0 hu hi
  · obtain ⟨rfl, hkind⟩ := readKind_live hka hl
    rcases hmove with hmove | ⟨hret, hown⟩
    · exact .account hkind hd hmove
    · have hnone := admit_retired ha hx (hxa.trans hret)
      rw [hxc] at hnone
      rw [hnone]
      exact .accountRetired hkind hd hown

/-- **B1 of every system whose kernel is the kernel**: each step of the audited log is a refusal
(which keeps every cell, `refuse_live`) or the kernel's derived and admitted Turn
(`step_authorized`); canonicity is carried along (`admit_cellsCanon`). -/
theorem authority_of_kernel [Std.TransOrd D] [Std.LawfulEqOrd D] (S : System D)
    (hrc : S.receive = receive S.X) (ha : S.admit = World.admit S.X.env)
    (hr : S.refuse = World.refuse S.X.env) : Integrity.authority S := by
  intro w w' l hau hcan v v' s hst
  have hd := hau.2
  clear hau
  revert hd hcan
  induction hst with
  | @here w₀ w₁ s₀ rest hs =>
      intro hcan hd id cell hl hne
      cases s₀ with
      | refusal r =>
          simp only [System.step, hr] at hs
          exact absurd ((refuse_live hs id).trans hl) hne
      | turn t =>
          simp only [System.step, ha] at hs
          obtain ⟨c, hdc, hc, -⟩ := hd
          refine ⟨t, c, rfl, hdc, hc, ?_⟩
          rw [hrc] at hc
          exact step_authorized hc hs hcan hl hne
  | @later w₀ w₁ v₀ v₁ s₀ s₁ rest hs _ ih =>
      intro hcan hd
      cases s₀ with
      | refusal r =>
          simp only [System.step] at hs
          obtain ⟨-, -, -, -, -, hnext⟩ := hd
          have hs' : World.refuse S.X.env w₀ r = .ok w₁ := hr ▸ hs
          intro id cell
          exact @ih (fun id cl hl => hcan id cl ((refuse_live hs' id).symm.trans hl)) (hnext _ hs) id cell
      | turn t =>
          simp only [System.step] at hs
          obtain ⟨-, -, -, hnext⟩ := hd
          have hs' : World.admit S.X.env w₀ t = .ok w₁ := ha ▸ hs
          intro id cell
          exact @ih (admit_cellsCanon hcan hs') (hnext _ hs) id cell

/-- **B1 of the deployed system.** -/
theorem top_integrity_authority (d : ByteArray → ByteArray) : Integrity.authority (deployed d) :=
  authority_of_kernel (deployed d) rfl rfl rfl

/-! ## The floor: the kernel whose `write` checks no owner -/

/-- A dispatched invoke is the signed body or below a signed invoke. -/
theorem dispatched_signed {X : Ctx D} {w : World D} {c : Call D} {n : Nat} {wk : Walk D} {a : D} {b : Body D}
    (h : Dispatched X w c n wk a b) :
    b = c.unsigned.body ∨ ∃ o m args budget via, c.unsigned.body = .invoke o m args budget via := by
  induction h with
  | root => exact .inl rfl
  | call _ _ _ _ _ _ _ ih =>
      rcases ih with h | h
      · exact .inr ⟨_, _, _, _, _, h.symm⟩
      · exact .inr h

/-- **The open write**: the create re-derives from the two-founder genesis; the deployed kernel
refuses founder 1's write of the object; the open kernel derives it (its event decodes to it) and
the kernel admits it; the object is live as an object, its cell changes, and its owner slot reads a
member other than the signer. -/
theorem run_open_write :
    (match rederiveLog Xd aGenesis aLog with
     | .ok w₁ =>
      (match receive Xd w₁ aWrite with | .error _ => true | .ok _ => false) &&
      match openReceive w₁ aWrite with
      | .ok tw =>
          match World.admit Xd.env w₁ tw with
          | .ok w₂ => decide (Xd.decodeCall tw.event = some aWrite) &&
              match w₁.live Xd.env aObj with
              | some cell => decide (cell.kind = kindObject) && decide (w₂.live Xd.env aObj ≠ some cell) &&
                  (match slotDigest Xd aObj cell slotOwner with
                   | .ok o => decide (o ≠ aWrite.unsigned.member)
                   | .error _ => false)
              | none => false
          | .error _ => false
      | .error _ => false
     | .error _ => false) = true := by
  native_decide

/-- **FLOOR (B1).** The claim refuses the kernel whose `write` checks no owner: an audited one-step
log from a canonical World (two founders' genesis and founder 0's create) in which founder 1, who
neither owns the object nor holds a grant, changes it. -/
theorem floor_integrity_authority (d : ByteArray → ByteArray) :
    ¬ Integrity.authority (openKernel d) := by
  intro h
  have hr := run_open_write
  cases ho : rederiveLog Xd aGenesis aLog with
  | error e => rw [ho] at hr; cases hr
  | ok w₁ =>
  rw [ho] at hr
  dsimp only at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨-, hr⟩ := hr
  have hcan : CellsCanon Xd.env w₁ := by
    have hs := (rederiveLog_sound ho).1
    unfold aGenesis at hs
    exact fold_cellsCanon (genesis_cellsCanon Xd _ _ _ _ _) hs
  have hb : aWrite.unsigned.body = .write aObj [(0, some "y".toUTF8)] none := rfl
  revert hr hb
  generalize aWrite = c
  generalize aObj = obj
  generalize [(0, some "y".toUTF8)] = edits
  intro hr hb
  cases htw : openReceive w₁ c with
  | error e => rw [htw] at hr; cases hr
  | ok tw =>
    rw [htw] at hr
    dsimp only at hr
    cases ha : World.admit Xd.env w₁ tw with
    | error e => rw [ha] at hr; cases hr
    | ok w₂ =>
      rw [ha] at hr
      dsimp only at hr
      simp only [Bool.and_eq_true] at hr
      obtain ⟨hd, hr⟩ := hr
      cases hl : w₁.live Xd.env obj with
      | none => rw [hl] at hr; cases hr
      | some cell =>
        rw [hl] at hr
        dsimp only at hr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
        obtain ⟨⟨hk, hch⟩, hown⟩ := hr
        cases hsd : slotDigest Xd obj cell slotOwner with
        | error e => rw [hsd] at hown; cases hown
        | ok o =>
          rw [hsd] at hown
          dsimp only at hown
          have hne : o ≠ c.unsigned.member := of_decide_eq_true hown
          have hs : (openKernel d).admit w₁ tw = .ok w₂ := ha
          have ha' : Audited (openKernel d) w₁ [.turn tw] w₂ :=
            ⟨by simp only [System.fold, System.step, hs],
              ⟨c, decide_eq_true_eq.mp hd, htw, fun _ _ => trivial⟩⟩
          have hst : StepAt (openKernel d) w₁ [.turn tw] w₁ (.turn tw) w₂ :=
            .here (by simp only [System.step, hs])
          obtain ⟨t', c', heq, hdc, -, hauth⟩ := h ha' hcan hst hl hch
          cases heq
          have hdc' : Xd.decodeCall tw.event = some c' := hdc
          rw [decide_eq_true_eq.mp hd] at hdc'
          cases hdc'
          have hauth' : Authorized Xd w₁ c obj cell (w₂.live Xd.env obj) := hauth
          revert hauth'
          generalize w₂.live Xd.env obj = after
          intro hauth'
          cases hauth' with
          | objectWrite _ hb' ho' hx =>
              rw [hb] at hb'
              cases hb'
              rw [hsd] at ho'
              cases ho'
              rcases hx with ⟨-, hm⟩ | ⟨g, hg, -⟩
              · exact hne hm.symm
              · cases hg
          | objectLaw _ hb' => rw [hb] at hb'; cases hb'
          | objectInvoke _ hd' =>
              rcases dispatched_signed hd' with h' | ⟨_, _, _, _, _, h'⟩
              · rw [hb] at h'; cases h'
              · rw [hb] at h'; cases h'
          | member hk' => exact absurd (hk.symm.trans hk') (by decide)
          | grantRetired hk' => exact absurd (hk.symm.trans hk') (by decide)
          | grantSpent hk' => exact absurd (hk.symm.trans hk') (by decide)
          | account hk' => exact absurd (hk.symm.trans hk') (by decide)
          | objectRetired _ hb' => rw [hb] at hb'; cases hb'
          | accountRetired hk' => exact absurd (hk.symm.trans hk') (by decide)

/-! ## Inhabited: the owner's write changes its object under the deployed kernel -/

/-- **The owner's write**: on the World the create re-derives to, the deployed kernel refuses
founder 1's write and derives founder 0's write (its event decodes to it) and admits it, and the object's cell changes. -/
theorem run_owner_write :
    (match rederiveLog Xd aGenesis aLog with
     | .ok w₁ =>
      (match receive Xd w₁ aWrite with | .error _ => true | .ok _ => false) &&
      match (deployed storeDigest).receive w₁ aOwnWrite with
      | .ok tw =>
          match (deployed storeDigest).admit w₁ tw with
          | .ok w₂ => decide (Xd.decodeCall tw.event = some aOwnWrite) &&
              match w₁.live Xd.env aObj with
              | some cell => decide (cell.kind = kindObject) && decide (w₂.live Xd.env aObj ≠ some cell)
              | none => false
          | .error _ => false
      | .error _ => false
     | .error _ => false) = true := by
  native_decide

/-- **INHABITED (B1).** The deployed system has an audited step, from a canonical World, that changes
a live object: the claim's premise is reached, by the owner. -/
theorem inhabited_authority :
    ∃ (w w' v v' : World Digest) (l : List (Step Digest)) (s : Step Digest) (id : Digest) (cell : Cell),
      Audited (deployed storeDigest) w l w' ∧ CellsCanon Xd.env w ∧ StepAt (deployed storeDigest) w l v s v' ∧
        v.live Xd.env id = some cell ∧ cell.kind = kindObject ∧ v'.live Xd.env id ≠ some cell := by
  have hr := run_owner_write
  cases ho : rederiveLog Xd aGenesis aLog with
  | error e => rw [ho] at hr; cases hr
  | ok w₁ =>
  rw [ho] at hr
  dsimp only at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨-, hr⟩ := hr
  have hcan : CellsCanon Xd.env w₁ := by
    have hs := (rederiveLog_sound ho).1
    unfold aGenesis at hs
    exact fold_cellsCanon (genesis_cellsCanon Xd _ _ _ _ _) hs
  revert hr
  generalize aOwnWrite = c
  generalize aObj = obj
  intro hr
  cases htw : (deployed storeDigest).receive w₁ c with
  | error e => rw [htw] at hr; cases hr
  | ok tw =>
    rw [htw] at hr
    dsimp only at hr
    cases ha : (deployed storeDigest).admit w₁ tw with
    | error e => rw [ha] at hr; cases hr
    | ok w₂ =>
      rw [ha] at hr
      dsimp only at hr
      simp only [Bool.and_eq_true] at hr
      obtain ⟨hd, hr⟩ := hr
      cases hl : w₁.live Xd.env obj with
      | none => rw [hl] at hr; cases hr
      | some cell =>
        rw [hl] at hr
        dsimp only at hr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
        obtain ⟨hk, hch⟩ := hr
        have ha' : Audited (deployed storeDigest) w₁ [.turn tw] w₂ :=
          ⟨by simp only [System.fold, System.step, ha], ⟨c, decide_eq_true_eq.mp hd, htw, fun _ _ => trivial⟩⟩
        have hst : StepAt (deployed storeDigest) w₁ [.turn tw] w₁ (.turn tw) w₂ :=
          .here (by simp only [System.step, ha])
        exact ⟨w₁, w₂, w₁, w₂, _, _, obj, cell, ha', hcan, hst, hl, hk, hch⟩

end Nanodregg.Spec
