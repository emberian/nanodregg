/-
# Protocol.Proofs.Settle — a `refused` reply is the final one (PROTOCOL-41)

* `final_iff_recorded`: a submit's reply is `refused` exactly when the call was recorded now, or its
  transaction id already holds a recorded refusal, or its window has passed. No other reply is final.
  Off the admitted arm this restates `verdictReply` (a specification, not a finality fact; that is
  `final_recorded`'s); on the admitted arm it uses the kernel (no record before, window open).
* `final_recorded`: a final reply inside the call's window leaves the call recorded in the World the
  Host keeps, under the name the reply states. That record is what makes every later submit
  `refusedFinal` (`Kernel.Receive.judge_recorded_final`, `fold_refused_retains`).
* `declined_open`: a `declined` reply recorded nothing, changed nothing, and the call's window has not
  passed. The attempt store keeps it open.
* `admitted_no_reply`: an admitted call gets no refusal reply.
-/
import Protocol.Settle
import Kernel.Proofs.Refusals
import Kernel.Proofs.Fold
import Kernel.Proofs.Receive
import Kernel.Proofs.Journal
import Protocol.Proofs.Command

namespace Nanodregg.Protocol.Settle

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

theorem judge_admitted {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (h : judge X w c = .admitted t w') : submit X w c = .ok (t, w') := by
  unfold judge judgeBy at h
  split at h
  · rename_i hs; cases h; exact hs
  · exfalso
    repeat' split at h
    all_goals cases h

/-- What the receive layer and the kernel say about an admitted call: nothing recorded at its id
before, and its window contains the next height. -/
theorem admitted_facts {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (h : judge X w c = .admitted t w') :
    refusedAnswer X w c = none ∧ w.height < c.unsigned.validUntil := by
  have hs := judge_admitted h
  obtain ⟨hj, hr, ha⟩ := submit_ok hs
  have hra : refusedAnswer X w c = none := by
    unfold submit at hs
    rw [hj] at hs
    simp only at hs
    split at hs
    · cases hs
    · assumption
  have hv := (receive_derived hr).validUntil
  have hw := (admit_window ha).2
  exact ⟨hra, by omega⟩

theorem admitted_no_reply {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {w' : World D} :
    verdictReply X w c (.admitted t w') = none := rfl

/-- **A reply is final exactly when the refusal is recorded, or was, or the window has passed.** -/
theorem final_iff_recorded {X : Ctx D} {w : World D} {c : Call D} {o : Outcome D}
    (hj : judge X w c = o) :
    (verdictReply X w c o).map Prod.fst = some .refused ↔
      (recordedNow o = true ∨ refusedAnswer X w c ≠ none ∨ c.unsigned.validUntil ≤ w.height) := by
  cases o with
  | admitted t w' =>
      obtain ⟨hra, hlt⟩ := admitted_facts hj
      simp only [verdictReply, Option.map_none, reduceCtorEq, false_iff, recordedNow,
        Bool.false_eq_true, hra, ne_eq, not_true_eq_false, false_or, Nat.not_le]
      exact hlt
  | recorded v r w' => simp [verdictReply, recordedNow]
  | declined v =>
      simp only [verdictReply, recordedNow, Bool.false_eq_true, false_or]
      cases hra : refusedAnswer X w c with
      | some code => simp
      | none =>
          by_cases hl : c.unsigned.validUntil ≤ w.height
          · simp [hl]
          · simp [hl]

/-- **A final reply inside the window is a record in the World the Host keeps**, under the reply's
own name (the recorded code names it, whenever it names anything). -/
theorem final_recorded {X : Ctx D} {w : World D} {c : Call D} {o : Outcome D} {n : String}
    (hj : judge X w c = o) (hr : verdictReply X w c o = some (.refused, n))
    (hin : w.height < c.unsigned.validUntil) :
    ∃ code, refusedAnswer X (keptWorld w o) c = some code ∧ ∀ m, codeName code = some m → m = n := by
  cases o with
  | admitted t w' => cases hr
  | recorded v r w' =>
      obtain ⟨-, -, rfl, href⟩ := judge_recorded hj
      simp only [verdictReply, Option.some.injEq, Prod.mk.injEq, true_and] at hr
      subst hr
      refine ⟨v.code, ?_, fun m hm => ?_⟩
      · have := refuse_recorded href
        simp only [keptWorld, refusedAnswer]
        rw [show (refusedOf X c v).txId = txIdOf X c from rfl] at this
        rw [this]; rfl
      · rw [codeName_code] at hm; exact (Option.some.inj hm).symm
  | declined v =>
      simp only [verdictReply] at hr
      cases hra : refusedAnswer X w c with
      | some code =>
          rw [hra] at hr
          simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hr
          refine ⟨code, hra, fun m hm => ?_⟩
          rw [hm] at hr; simpa using hr
      | none =>
          rw [hra] at hr
          have hl : ¬ c.unsigned.validUntil ≤ w.height := by omega
          simp [hl] at hr

/-- **`declined` is open**: nothing was recorded, the World is unchanged, nothing was recorded for
this call before, and its window has not passed. -/
theorem declined_open {X : Ctx D} {w : World D} {c : Call D} {o : Outcome D} {n : String}
    (hr : verdictReply X w c o = some (.declined, n)) :
    (∃ v, o = .declined v ∧ v.name = n) ∧ keptWorld w o = w ∧ refusedAnswer X w c = none ∧
      w.height < c.unsigned.validUntil := by
  cases o with
  | admitted t w' => cases hr
  | recorded v r w' => simp [verdictReply] at hr
  | declined v =>
      simp only [verdictReply] at hr
      cases hra : refusedAnswer X w c with
      | some code => rw [hra] at hr; simp at hr
      | none =>
          rw [hra] at hr
          by_cases hl : c.unsigned.validUntil ≤ w.height
          · simp [hl] at hr
          · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and] at hr
            exact ⟨⟨v, rfl, hr⟩, rfl, rfl, by omega⟩

/-! ## The member's settlement (PROTOCOL-46)

What `ofReceipt` says of a receipt follow built from its own World (`Receipt.build`):

* `settle_committed`: `committed h td` is the World's journal entry at the id;
* `settle_final_never_admits`: `refused` or `expired` is final: no World a later log reaches from it
  admits the call (`submit`). Proved from the World alone: the recorded refusal stays below its prune
  height (`Kernel.fold_refused_retains`) and the call's window has closed by then (the checkable arm
  `validUntil ≤ h + 2 · windowMax`); `expired` by the window alone;
* `settle_open_not_final`: every call some World would still admit settles `open` there, never final
  and never "safe to run again": the old terminal `absent` said that of exactly these calls.
-/

section Member

/-- What `build` answers, read from the World. -/
theorem build_answer (E : Env D) (w : World D) (tx : D) :
    (Receipt.build E w tx).answer = match w.journalAt E tx with
      | some (h, td) => .committed h td
      | none => match w.refusalAt E (.tx tx) with
        | some (.refused h code m) => .refused h code m
        | _ => .absent := rfl

/-- **A committed settlement is the World's journal entry.** -/
theorem settle_committed {E : Env D} {w : World D} {tx : D} {fg b : Bool} {H vu h : Nat} {td : D}
    (hv : ofReceipt fg b H vu (Receipt.build E w tx).answer = .committed h td) :
    w.journalAt E tx = some (h, td) := by
  rw [build_answer] at hv
  split at hv
  · rename_i h' td' hj
    simp only [ofReceipt, Verdict.committed.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact hj
  · split at hv
    · simp only [ofReceipt] at hv; split at hv <;> cases hv
    · simp only [ofReceipt] at hv
      repeat' split at hv
      all_goals cases hv

/-- An admitted call's World: nothing at its id, and its window contains the next height and closes
within `windowMax` of its `notBefore`. -/
theorem submit_facts {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hs : submit X w c = .ok (t, w')) :
    w.journalAt X.env (txIdOf X c) = none ∧ refusedAnswer X w c = none ∧
      w.height < c.unsigned.validUntil ∧ c.unsigned.validUntil ≤ c.unsigned.notBefore + Bounds.windowMax := by
  obtain ⟨hj, hr, ha⟩ := submit_ok hs
  have hra : refusedAnswer X w c = none := by
    unfold submit at hs
    rw [hj] at hs
    simp only at hs
    split at hs
    · cases hs
    · assumption
  obtain ⟨_, _, _, _, _, _, hnb, hvu⟩ := receive_derived hr
  have hw := admit_window ha
  have hb := admit_bounded ha
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hwm
  refine ⟨hj, hra, by omega, by omega⟩

/-- **A final settlement of the record and window arms is never admitted** (`refused CODE` from a
recorded refusal, or `expired`, from the member's own World, at `behind = false`): no World any later
log reaches from it admits the call. The stale arm (`behind = true`, `refused staleCode`, KERNEL-54)
is NOT covered here: its finality rests on `Kernel.stale_behind_forever` (`settleOf_stale` says when
it is said). -/
theorem settle_final_never_admits {X : Ctx D} {w w' : World D} {c : Call D} {l : List (Kernel.Step D)}
    (hc : w.RefusalsCanon X.env) (hjc : w.JournalCanon X.env)
    (hv : ofReceipt (journalForgets w.height c.unsigned.notBefore) false w.height c.unsigned.validUntil
        (Receipt.build X.env w (txIdOf X c)).answer = .expired ∨
      ∃ code, ofReceipt (journalForgets w.height c.unsigned.notBefore) false w.height c.unsigned.validUntil
        (Receipt.build X.env w (txIdOf X c)).answer = .refused code)
    (hf : World.fold X.env w l = .ok w') : ∀ out, submit X w' c ≠ .ok out := by
  intro ⟨t, w''⟩ hs
  obtain ⟨-, hra, hlt, -⟩ := submit_facts hs
  have hh := fold_height hf
  rw [build_answer] at hv
  split at hv
  · rcases hv with hv | ⟨_, hv⟩ <;> cases hv
  · rename_i hj
    split at hv
    · rename_i hh₀ code _ hr
      simp only [ofReceipt] at hv
      split at hv
      · rename_i hwin
        by_cases hp : w'.height < hh₀ + 2 * Bounds.windowMax
        · obtain ⟨hr', -⟩ := fold_refused_retains hc hjc hf hr hj hp
          unfold refusedAnswer at hra
          rw [hr'] at hra
          cases hra
        · omega
      · rcases hv with hv | ⟨_, hv⟩ <;> cases hv
    · simp only [ofReceipt, Bool.false_eq_true, ↓reduceIte] at hv
      split at hv
      · rcases hv with hv | ⟨_, hv⟩ <;> cases hv
      · split at hv
        · omega
        · rcases hv with hv | ⟨_, hv⟩ <;> cases hv

/-- **An admissible call settles `open`, never final**: wherever `submit` would still admit the call,
the member's own settlement of it there is `open`. So a run that ends on `absent` with the call's
window live must leave the attempt open: the signed bytes, held by the Host or any relay, may still
be admitted, and a re-signed command would make a second call beside it (the deleted terminal
`absent` said "running the command again is safe" of exactly these calls). -/
theorem settle_open_not_final {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hs : submit X w c = .ok (t, w')) :
    ofReceipt (journalForgets w.height c.unsigned.notBefore) false w.height c.unsigned.validUntil
      (Receipt.build X.env w (txIdOf X c)).answer = .open := by
  obtain ⟨hj, hra, hlt, hwm⟩ := submit_facts hs
  have hnf : journalForgets w.height c.unsigned.notBefore = false := by
    simp only [journalForgets, decide_eq_false_iff_not]
    rw [windowMax_eq] at hwm
    rw [windowMax_eq]
    omega
  have hnot : ¬ c.unsigned.validUntil ≤ w.height := by omega
  unfold refusedAnswer at hra
  rw [build_answer]
  simp only [hj]
  cases hr : w.refusalAt X.env (.tx (txIdOf X c)) with
  | none => simp [ofReceipt, hnf, hnot]
  | some leaf =>
      cases leaf with
      | refused h code m => simp [hr] at hra
      | count n => simp [ofReceipt, hnf, hnot]

end Member

/-- **`settle_final_never_admits` on every World folded from a genesis (`Receive.genesisWorld`)**: a call settled
`expired` or `refused` from the receipt follow built there is admitted by no later World. -/
theorem settle_final_reached {X : Ctx D} {name nonce : ByteArray} {a : Nat} {fs : List (ByteArray × D)}
    {l₀ : List (Kernel.Step D)} {w w' : World D} {c : Call D} {l : List (Kernel.Step D)}
    (hw : World.fold X.env (genesisWorld X name nonce a fs) l₀ = .ok w)
    (hv : ofReceipt (journalForgets w.height c.unsigned.notBefore) false w.height c.unsigned.validUntil
        (Receipt.build X.env w (txIdOf X c)).answer = .expired ∨
      ∃ code, ofReceipt (journalForgets w.height c.unsigned.notBefore) false w.height c.unsigned.validUntil
        (Receipt.build X.env w (txIdOf X c)).answer = .refused code)
    (hf : World.fold X.env w l = .ok w') : ∀ out, submit X w' c ≠ .ok out :=
  settle_final_never_admits (fold_refusalsOk (genesisWorld_refusalsOk X name nonce a fs) hw).1
    (fold_journalOk (genesisWorld_journalOk X name nonce a fs) hw).1 hv hf

/-- **The deployed settlement of an admissible call is `open`** (KERNEL-54): with `behind` follow's
own `staleBehind`, wherever `submit` admits the call the settlement `receipt CALL` prints is `open`,
never final (`settle_open_not_final` composed with `Command.staleBehind_admissible`). -/
theorem settleOf_admissible_open {X : Ctx D} {me : Command.Self D} {w w' : World D} {c : Call D}
    {t : Turn D} (hs : submit X w c = .ok (t, w')) : Command.settleOf X me w c = .open := by
  unfold Command.settleOf
  rw [Command.staleBehind_admissible hs]
  exact settle_open_not_final hs

/-- **`refused stale` without a record is said only of a stale-BEHIND call** (KERNEL-54): where the
receipt finds neither a journal entry nor a recorded refusal at the id, the settlement is
`refused staleCode` only when follow's own fold says `staleBehind` (`Command.staleBehind_spec`). -/
theorem settleOf_stale {X : Ctx D} {me : Command.Self D} {w : World D} {c : Call D}
    (ha : (Receipt.build X.env w (txIdOf X c)).answer = .absent)
    (hv : Command.settleOf X me w c = .refused staleCode) : Command.staleBehind X me w c = true := by
  unfold Command.settleOf at hv
  rw [ha] at hv
  simp only [ofReceipt] at hv
  repeat' split at hv
  all_goals first | assumption | cases hv

/-! ## The refused arm never answers `open` on a World follow absorbed from a genesis (`Receive.genesisWorld`)

KERNEL records a refusal only for a call whose window is no wider than an admissible call's
(8ad3982, `Kernel.refuse_window_width`): the leaf records `h = w.height + 1` and the call's
`validUntil ≤ h + windowMax`. Follow takes a refusal only as the one its own `judge` records for the
call it decoded, or its own `cancel` records for it under the event's signature (KERNEL-60,
PROTOCOL-60: the record is `recordOf` the call with that signature) (`Command.absorbStep`), so on a World follow absorbed (`WindowedIn S`, `S` the steps
follow took) every refusal leaf at a transaction id is the leaf of a call in `S` with that id whose
window closes within `windowMax` of `h`. The member's own call has that id: either its window closes
by `h + windowMax` and `ofReceipt` answers `refused` (`h + windowMax ≤ h + 2 · windowMax`), or `S`
itself holds a DIFFERENT call (a narrower window) under the member's transaction id: a hash collision
in follow's own log, or the member's call is outside the codec's domain (`callBytes` is injective
only on calls that fit it).

A World carried from a base (`adopt`, an opened Store) is not covered: its refusal leaves keep only
`(h, code)`, not the call. There, `ofReceipt`'s own check is what keeps the arm safe.

* `absorbPage_windowedIn`, `absorbed_windowedIn` (from `genesisWorld_windowedIn`): the invariant
  along follow's absorption;
* `windowedIn_refused`: the member's call refused at `h` closes by `h + windowMax`, or `S` holds a
  colliding call;
* `settle_refused_final`: the refused arm answers `refused`, or `S` holds a colliding call;
  `settle_refused_absorbed`: the same with `S` exactly the steps follow took from a genesis.
-/

section Windowed

/-- Every recorded refusal on `w` is a record of a call (`recordOf`: a judged refusal's, with no
cancel signature, or a cancel's, with one) that a refusal step of `S` carries, at that call's id,
and the call's window closes within `windowMax` of the record's height; and the refusals are
`RefusalsOk`. -/
def WindowedIn (X : Ctx D) (S : List (Kernel.Step D)) (w : World D) : Prop :=
  w.RefusalsOk X.env ∧ ∀ id h code mb, w.refusalAt X.env (.tx id) = some (.refused h code mb) →
    ∃ c v a, Kernel.Step.refusal (recordOf X c v a) ∈ S ∧ txIdOf X c = id ∧
      c.unsigned.validUntil ≤ h + Bounds.windowMax

theorem windowedIn_mono {X : Ctx D} {S S' : List (Kernel.Step D)} {w : World D} (hs : ∀ s ∈ S, s ∈ S')
    (hw : WindowedIn X S w) : WindowedIn X S' w := by
  refine ⟨hw.1, fun id h code mb hk => ?_⟩
  obtain ⟨c, v, a, hm, hid, hvu⟩ := hw.2 id h code mb hk
  exact ⟨c, v, a, hs _ hm, hid, hvu⟩

/-- The World a genesis builds records no refusal (founders are trie entries only). -/
theorem genesisWorld_windowedIn (X : Ctx D) (S : List (Kernel.Step D)) (name nonce : ByteArray) (a : Nat)
    (fs : List (ByteArray × D)) : WindowedIn X S (genesisWorld X name nonce a fs) := by
  refine ⟨genesisWorld_refusalsOk X name nonce a fs, fun id h code mb hk => ?_⟩
  have he : (genesisWorld X name nonce a fs).refusals = .empty := rfl
  unfold World.refusalAt at hk
  rw [he] at hk
  cases hk

/-- An admission keeps every refusal leaf or prunes it; it records none. -/
theorem admit_windowedIn {X : Ctx D} {S : List (Kernel.Step D)} {w w' : World D} {t : Turn D}
    (hw : WindowedIn X S w) (h : World.admit X.env w t = .ok w') : WindowedIn X S w' := by
  refine ⟨admit_refusalsOk hw.1 h, fun id hh code mb hk => ?_⟩
  rw [admit_refusalAt hw.1.1 h] at hk
  split at hk
  · exact hw.2 id hh code mb (Option.filter_eq_some_iff.mp hk).1
  · exact hw.2 id hh code mb hk

/-- A record `World.refuse` takes for a call (`recordOf`, any cancel field) adds its call's leaf,
inside the window bound, carried by the step. -/
theorem refuse_windowedIn {X : Ctx D} {S : List (Kernel.Step D)} {w w' : World D} {c : Call D}
    {v : Receive.Verdict D} {a : ByteArray}
    (hw : WindowedIn X S w) (href : World.refuse X.env w (recordOf X c v a) = .ok w') :
    WindowedIn X (S ++ [.refusal (recordOf X c v a)]) w' := by
  refine ⟨refuse_refusalsOk hw.1 href, fun id hh code mb hk => ?_⟩
  have hwid := refuse_window_width href
  rw [refuse_refusalAt href] at hk
  split at hk
  · rename_i he; cases he
  split at hk
  · rename_i he; cases he
  · split at hk
    · rename_i _ he
      injection he with he
      injection hk with hk
      injection hk with h1 h2 h3
      subst he h1 h3
      exact ⟨c, v, a, by simp, rfl, hwid⟩
    · obtain ⟨c', v', a', hm, hid, hvu⟩ := hw.2 id hh code mb hk
      exact ⟨c', v', a', by simp [hm], hid, hvu⟩

/-- A refusal `judge` records adds its call's leaf, inside the window bound, carried by the step. -/
theorem judge_windowedIn {X : Ctx D} {S : List (Kernel.Step D)} {w w' : World D} {c : Call D}
    {v : Receive.Verdict D} {r : Refused D}
    (hw : WindowedIn X S w) (hj : judge X w c = .recorded v r w') :
    WindowedIn X (S ++ [.refusal r]) w' := by
  obtain ⟨-, -, rfl, href⟩ := judge_recorded hj
  exact refuse_windowedIn hw href

/-- A cancel `cancel` records adds its call's leaf, inside the window bound, carried by the step. -/
theorem cancel_windowedIn {X : Ctx D} {S : List (Kernel.Step D)} {w w' : World D} {c : Call D}
    {sig : ByteArray} {v : Receive.Verdict D} {r : Refused D}
    (hw : WindowedIn X S w) (hc : Receive.cancel X w c sig = .recorded v r w') :
    WindowedIn X (S ++ [.refusal r]) w' := by
  obtain ⟨-, -, rfl, href⟩ := cancel_recorded hc
  exact refuse_windowedIn hw href

/-- One step follow absorbs keeps the invariant, with the step taken. -/
theorem absorbStep_windowedIn {X : Ctx D} {S : List (Kernel.Step D)} {w w' : World D} {e : ByteArray}
    {s : Kernel.Step D} (hw : WindowedIn X S w) (h : Command.absorbStep X w e = .ok (s, w')) :
    WindowedIn X (S ++ [s]) w' := by
  obtain ⟨ev, -, hr⟩ := Command.absorbStep_ok.mp h
  rcases rederive_ok hr with ⟨b, c, t, -, -, hs, rfl⟩ | ⟨b, c, v, r, -, -, hj, rfl⟩ |
      ⟨sig, b, c, v, r, -, -, hco, rfl⟩
  · exact windowedIn_mono (fun _ hm => by simp [hm]) (admit_windowedIn hw (submit_ok hs).2.2)
  · exact judge_windowedIn hw hj
  · exact cancel_windowedIn hw hco

theorem absorb_windowedIn {X : Ctx D} {S : List (Kernel.Step D)} :
    ∀ (evs : List ByteArray) {w w' : World D} {acc ts : Array (Kernel.Step D × D)},
      WindowedIn X (S ++ acc.toList.map Prod.fst) w → Command.absorb X w acc evs = .ok (w', ts) →
        WindowedIn X (S ++ ts.toList.map Prod.fst) w'
  | [], w, w', acc, ts, hw, h => by
    simp only [Command.absorb, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hw
  | e :: es, w, w', acc, ts, hw, h => by
    unfold Command.absorb at h
    split at h
    · rename_i s w₁ hs
      refine absorb_windowedIn es (windowedIn_mono (fun x hm => ?_) (absorbStep_windowedIn hw hs)) h
      simpa [List.append_assoc] using hm
    · cases h

/-- **The invariant along every page follow absorbs**, with the page's steps taken. -/
theorem absorbPage_windowedIn {X : Ctx D} {S : List (Kernel.Step D)} {w w' : World D}
    {evs : List ByteArray} {steps base : Nat} {chain : ByteArray} {ts : List (Kernel.Step D × D)}
    {wb? : Option (World D)} (hw : WindowedIn X S w)
    (h : Command.absorbPage X w evs steps chain base = .ok (w', ts, wb?)) :
    WindowedIn X (S ++ ts.map Prod.fst) w' := by
  obtain ⟨wb, tb, ts', h₁, h₂, rfl, -, -⟩ := Command.absorbPage_ok h
  have h0 : WindowedIn X (S ++ (#[] : Array (Kernel.Step D × D)).toList.map Prod.fst) w := by simpa using hw
  exact absorb_windowedIn _ (absorb_windowedIn _ h0 h₁) h₂

/-- **The member's call, refused at `h` on a `WindowedIn S` World, closes within `windowMax` of `h`**,
or a refusal step of `S` carries a different call (its window closes earlier) under the member's
transaction id. -/
theorem windowedIn_refused {X : Ctx D} {S : List (Kernel.Step D)} {w : World D} {c : Call D}
    {h code : Nat} {m : D} (hw : WindowedIn X S w)
    (hr : (Receipt.build X.env w (txIdOf X c)).answer = .refused h code m) :
    c.unsigned.validUntil ≤ h + Bounds.windowMax ∨
      ∃ c' v a, Kernel.Step.refusal (recordOf X c' v a) ∈ S ∧ txIdOf X c' = txIdOf X c ∧
        c'.unsigned.validUntil < c.unsigned.validUntil := by
  rw [build_answer] at hr
  split at hr
  · cases hr
  · split at hr
    · rename_i h' code' m' hk
      injection hr with e1 e2 e3
      subst e1 e2 e3
      obtain ⟨c', v, a, hm, hid, hvu⟩ := hw.2 _ _ _ _ hk
      by_cases hle : c.unsigned.validUntil ≤ h' + Bounds.windowMax
      · exact .inl hle
      · exact .inr ⟨c', v, a, hm, hid, by omega⟩
    · cases hr

/-- **The refused arm's `open` is dead** on a `WindowedIn S` World: a receipt that refuses the member's
own call settles `refused`, unless `S` carries a colliding call. -/
theorem settle_refused_final {X : Ctx D} {S : List (Kernel.Step D)} {w : World D} {c : Call D}
    {fg b : Bool} {H h code : Nat} {m : D} (hw : WindowedIn X S w)
    (hr : (Receipt.build X.env w (txIdOf X c)).answer = .refused h code m) :
    ofReceipt fg b H c.unsigned.validUntil (Receipt.build X.env w (txIdOf X c)).answer = .refused code ∨
      ∃ c' v a, Kernel.Step.refusal (recordOf X c' v a) ∈ S ∧ txIdOf X c' = txIdOf X c ∧
        c'.unsigned.validUntil < c.unsigned.validUntil := by
  rcases windowedIn_refused hw hr with hv | hcol
  · left
    rw [hr]
    simp only [ofReceipt]
    rw [if_pos (by omega)]
  · exact .inr hcol

/-- Follow's absorption from `w`: a run of pages, each taken by `absorbPage`, and `S` the steps they
took, in order. -/
inductive Absorbed (X : Ctx D) : World D → List (Kernel.Step D) → World D → Prop
  | nil (w : World D) : Absorbed X w [] w
  | page {w w' w'' : World D} {evs : List ByteArray} {steps base : Nat} {chain : ByteArray}
      {ts : List (Kernel.Step D × D)} {wb? : Option (World D)} {S : List (Kernel.Step D)}
      (h : Command.absorbPage X w evs steps chain base = .ok (w', ts, wb?)) (rest : Absorbed X w' S w'') :
      Absorbed X w (ts.map Prod.fst ++ S) w''

theorem absorbed_windowedIn {X : Ctx D} {S₀ S : List (Kernel.Step D)} {w w' : World D}
    (hw : WindowedIn X S₀ w) (h : Absorbed X w S w') : WindowedIn X (S₀ ++ S) w' := by
  induction h generalizing S₀ with
  | nil => simpa using hw
  | page hp _ ih => simpa [List.append_assoc] using ih (absorbPage_windowedIn hw hp)

/-- **The refused arm's `open` is dead on the World follow absorbed from a genesis**, with `S` the
steps follow itself took: a receipt refusing the member's call settles `refused`, unless follow's own
log carries a different call (a narrower window) under the member's transaction id. -/
theorem settle_refused_absorbed {X : Ctx D} {name nonce : ByteArray} {a : Nat}
    {fs : List (ByteArray × D)} {S : List (Kernel.Step D)} {w : World D} {c : Call D} {fg b : Bool}
    {H h code : Nat} {m : D} (ha : Absorbed X (genesisWorld X name nonce a fs) S w)
    (hr : (Receipt.build X.env w (txIdOf X c)).answer = .refused h code m) :
    ofReceipt fg b H c.unsigned.validUntil (Receipt.build X.env w (txIdOf X c)).answer = .refused code ∨
      ∃ c' v sg, Kernel.Step.refusal (recordOf X c' v sg) ∈ S ∧ txIdOf X c' = txIdOf X c ∧
        c'.unsigned.validUntil < c.unsigned.validUntil :=
  settle_refused_final (by simpa using absorbed_windowedIn (genesisWorld_windowedIn X [] name nonce a fs) ha) hr

end Windowed

end Nanodregg.Protocol.Settle
