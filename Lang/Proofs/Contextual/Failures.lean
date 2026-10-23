/-
# Lang.Proofs.Contextual.Failures — lost replies over the deployed objects (PROT-5, LANG-75.16)

The protocol calculus's `Hist.inflight` is a dispatched call whose reply was lost. In the deployed
system that state has two owners, and they differ in one Boolean (`Nano.Peer.reliable`, Barwell
et al.'s reliable roles; Graversen–Montesi–Peressotti's at-most-once with the frame identity = the
call digest):

* the KERNEL is reliable. `submit_at_most_once`: once `Receive.submit` admitted a signed call, no
  later World of the log admits it again, and while its journal entry is kept a retry of the same
  bytes is answered `replayed` at the height it committed, whatever the World is now (the
  journal-first recognition in `Kernel/Receive/Submit.lean`: a lost reply is RECOVERED by retrying).
  `reach_submit_at_most_once`: from a genesis, no premise.
* KEYBROKER is unreliable: it charges the meter per ask and deduplicates nothing, so the resident
  never sends a spent ask again. `lost_ask_keeps_obligation`: on every path of a tick, an ask that
  ended `lost` is the tick's only ask, and the only answer the tick may invoke is
  `(unanswered WHY)` for that ring: the obligation (the ring gets an answer) stands, and nothing is
  re-planned in its place (the deployed form of the calculus's `lost_reply_*`).
* `lost_reply_policy`: for each peer, by its Boolean: a reliable peer's lost reply leaves the
  request kept, so the next tick sends it again while the ring is pending (`LostKept`: an invoke
  whose reply never came back leaves its answer kept and `decideTick` re-delivers it); an
  unreliable peer's lost request is never sent again before something freed its ring
  (`LostSpent`, from `Hosting.Proofs.BellConform.bell_resident_conforms`). Flip either Boolean and
  the theorem is false: a lost answered-ask is forgotten once its `unanswered` text is taken, and a
  lost invoke is re-sent with the ring still pending.

The resident's re-delivery after a lost invoke is a FRESH signed call, so the journal does not
recognise it; what makes it safe is the bell's `answered` guard (`rung: answered`) and the
resident's re-read (`DeliverAfter`), not `submit_at_most_once`. The latter is the reliability of an
exact retry (a client re-sending the bytes whose reply it lost). This module replaces the
calculus's private delivery model (`External`, `Internal`, `Consistent` and the theorems over them,
deleted): the deployed objects state the failures themselves.
-/
import Lang.Proofs.Contextual.Protocol
import Hosting.Proofs.BellConform
import Kernel.Proofs.Journal

namespace Nanodregg.Lang.Contextual.Protocol.Failures

/-! ## The kernel: an exact retry is recognised, never re-admitted -/

section Kernel

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- **At most once across a lost reply** (B9). After `submit` admitted call `c` from `w₀`, no World
the log reaches admits `c` again; and until `journalForgets` (the call's own window plus the
journal's retention) a retry of `c` is answered `replayed` at the height it committed
(`w₀.height + 1`), without re-deriving it against the World it meets. -/
theorem submit_at_most_once {X : Kernel.Receive.Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {t : Turn D}
    {l : List (Kernel.Step D)} (hc : w₀.JournalCanon X.env) (h₁ : submit X w₀ c = .ok (t, w₁))
    (hf : World.fold X.env w₁ l = .ok w₂) :
    (∀ r, submit X w₂ c ≠ .ok r) ∧
      (journalForgets w₂.height c.unsigned.notBefore = false →
        submit X w₂ c = .error (.rejected (.replayed (w₀.height + 1)))) := by
  refine ⟨submit_once hc h₁ hf, fun hnf => ?_⟩
  obtain ⟨_, hr, ha⟩ := submit_ok h₁
  have hd := receive_derived hr
  have hj := fold_answers hc ha hf (by rw [hd.notBefore]; exact hnf)
  rw [hd.txId] at hj
  exact submit_replayed hj

/-- **From a genesis, at most once across a lost reply** (`submit_at_most_once`, no premise). -/
theorem reach_submit_at_most_once {X : Kernel.Receive.Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {l₀ l : List (Kernel.Step D)} {w₀ w₁ w₂ : World D} {c : Call D}
    {t : Turn D} (h₀ : World.fold X.env (genesisWorld X name nonce allowance founders) l₀ = .ok w₀)
    (h₁ : submit X w₀ c = .ok (t, w₁)) (hf : World.fold X.env w₁ l = .ok w₂) :
    (∀ r, submit X w₂ c ≠ .ok r) ∧
      (journalForgets w₂.height c.unsigned.notBefore = false →
        submit X w₂ c = .error (.rejected (.replayed (w₀.height + 1)))) :=
  submit_at_most_once (reach_journalOk h₀).1 h₁ hf

end Kernel

/-! ## The resident's two peers -/

section Resident

open Nanodregg.Hosting Nanodregg.Hosting.Resident Nanodregg.Hosting.Proofs.ResidentRun
open Nanodregg.Hosting.Proofs.BellConform Nanodregg.Lang.Contextual.Protocol.Nano

/-- A reliable peer's lost reply leaves the request kept: on every path of a tick that goes on, an
effect to `p` about ring `r` whose reply was lost leaves an answer for `r` kept, and every later
read that still lists `r` re-delivers exactly it. -/
def LostKept (p : Peer) : Prop :=
  ∀ (w : Where) (m m' : Mem) (es : List Ev) (e : Ev) (r : Ring),
    Hosting.Proofs.ResidentRun.Runs (tickP w m) es (.next m') → e ∈ core es → lostReply e = true → p.req e = some r →
      ∃ t, m'.kept = some (r, t) ∧ ∀ ps, r ∈ ps → decideTick ps m'.kept = .answer r t

/-- An unreliable peer's lost request is never sent again: on every chain of ticks, between an
effect to `p` about `r` whose reply was lost and a later effect to `p` about `r`, something freed `r`. -/
def LostSpent (p : Peer) : Prop :=
  ∀ (w : Where) (m : Mem) (ess : List (List Ev)) (pre mid post : List Ev) (e₁ e₂ : Ev) (r : Ring),
    Ticks w m ess → core ess.flatten = pre ++ e₁ :: mid ++ e₂ :: post →
      lostReply e₁ = true → p.req e₁ = some r → p.req e₂ = some r → ∃ f ∈ mid, Frees r f

private theorem req_kernel {e : Ev} {r : Ring} (h : Peer.req .kernel e = some r) :
    ∃ sh t x, e = .cmd (.invoke sh r t) x := by
  cases e with
  | cmd c x =>
    cases c with
    | invoke sh r' t =>
      simp only [Peer.req, Option.some.injEq] at h
      exact ⟨sh, t, x, by rw [h]⟩
    | _ => simp [Peer.req] at h
  | _ => simp [Peer.req] at h

private theorem req_broker {e : Ev} {r : Ring} (h : Peer.req .broker e = some r) :
    ∃ q x, e = .ask r q x := by
  cases e with
  | ask r' q x =>
    simp only [Peer.req, Option.some.injEq] at h
    exact ⟨q, x, by rw [h]⟩
  | cmd c x => cases c <;> simp [Peer.req] at h
  | _ => simp [Peer.req] at h

private theorem mem_invokes {l : List Ev} {sh : Shape} {r : Ring} {t : ByteArray}
    {x : Except String Reply} (h : Ev.cmd (.invoke sh r t) x ∈ l) : (r, t) ∈ invokes l :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

private theorem mem_asks {l : List Ev} {r : Ring} {q : Broker.Ask} {x : AskEnd}
    (h : Ev.ask r q x ∈ l) : r ∈ asks l :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

private theorem asks_one {pre post : List Ev} {sh : Shape} {y : Except String Reply} {r r₀ : Ring}
    {x : AskEnd} {c : Conf}
    (h : asks (pre ++ .cmd (.read sh) y :: .keep r₀ intentText true :: .ask r₀ (askOf c r₀) x :: post) =
      [r]) : asks pre = [] ∧ asks post = [] := by
  have := congrArg List.length h
  simp only [asks, List.filterMap_append, List.filterMap_cons, List.length_append,
    List.length_cons, List.length_nil] at this
  constructor
  · exact List.length_eq_zero_iff.mp (by simp only [asks]; omega)
  · exact List.length_eq_zero_iff.mp (by simp only [asks]; omega)

/-- In a delivery, a lost invoke is the delivery's own, and nothing after it is kept or forgotten. -/
private theorem deliver_lost {sh : Shape} {r : Ring} {t : ByteArray} {l : List Ev}
    (h : DeliverCore sh r t l) {sh' : Shape} {r' : Ring} {t' : ByteArray} {s : String}
    (hm : Ev.cmd (.invoke sh' r' t') (.error s) ∈ l) (k : Option (Ring × ByteArray)) :
    r' = r ∧ t' = t ∧ keptAfter k l = k := by
  have hi := (deliver_counts h).2.1
  obtain ⟨x, rest, rfl, hd⟩ := h
  rcases List.mem_cons.mp hm with he | hm'
  · cases he
    simp only [DeliverAfter] at hd
    subst hd
    exact ⟨rfl, rfl, rfl⟩
  · have := mem_invokes hm'
    have hr : invokes rest = [] := by simpa [invokes] using hi
    rw [hr] at this
    cases this

/-- In a tick's act, a lost invoke of `(r, t)` leaves `(r, t)` kept. -/
private theorem act_lost {c : Conf} {sh : Shape} {k : Option (Ring × ByteArray)} {p : List Ring}
    {l : List Ev} (h : ActCore c sh k p l) {sh' : Shape} {r : Ring} {t : ByteArray} {s : String}
    (hm : Ev.cmd (.invoke sh' r t) (.error s) ∈ l) : keptAfter k l = some (r, t) := by
  unfold ActCore at h
  split at h
  · rcases h with ⟨-, b, rfl⟩ | ⟨-, rfl⟩ <;> simp at hm
  · rename_i r₀ t₀ hd
    obtain ⟨rfl, rfl, hk⟩ := deliver_lost h hm k
    rw [hk]
    exact (Nanodregg.Hosting.Proofs.Resident.decide_answer hd).1
  · rename_i r₀ hd
    rcases h with rfl | ⟨x, rest, rfl, ha⟩
    · simp at hm
    · unfold AfterAsk at ha
      split at ha
      · obtain ⟨b, rfl⟩ := ha
        simp at hm
      · rename_i t₁ ht
        rcases ha with rfl | ⟨rest', rfl, hd'⟩
        · simp at hm
        · have hm' : Ev.cmd (.invoke sh' r t) (.error s) ∈ rest' := by simpa using hm
          obtain ⟨rfl, rfl, hk⟩ := deliver_lost hd' hm' (some (r₀, t₁))
          simpa [keptAfter] using hk

/-- In a tick's core, a lost invoke of `(r, t)` leaves `(r, t)` kept. -/
private theorem tick_lost {c : Conf} {m : Mem} {l : List Ev} (h : TickCore c m l) {sh' : Shape}
    {r : Ring} {t : ByteArray} {s : String} (hm : Ev.cmd (.invoke sh' r t) (.error s) ∈ l) :
    keptAfter m.kept l = some (r, t) := by
  have read_lost : ∀ {sh : Shape} {l : List Ev}, ReadCore c sh m.kept l →
      Ev.cmd (.invoke sh' r t) (.error s) ∈ l → keptAfter m.kept l = some (r, t) := by
    intro sh l h hm
    obtain ⟨y, rest, rfl, hr⟩ := h
    split at hr
    · subst hr; simp at hm
    · have hm' : Ev.cmd (.invoke sh' r t) (.error s) ∈ rest := by simpa using hm
      simpa [keptAfter] using act_lost hr hm'
  unfold TickCore at h
  split at h
  · exact read_lost h hm
  · obtain ⟨y, rest, rfl, hr⟩ := h
    split at hr
    · subst hr; simp at hm
    · have hm' : Ev.cmd (.invoke sh' r t) (.error s) ∈ rest := by simpa using hm
      simpa [keptAfter] using read_lost hr hm'

/-- **The kernel is reliable**: a lost invoke leaves its answer kept for the next tick. -/
theorem kernel_lost_kept : LostKept .kernel := by
  intro w m m' es e r h he hl hr
  obtain ⟨sh, t, x, rfl⟩ := req_kernel hr
  obtain ⟨s, rfl⟩ : ∃ s, x = .error s := by
    cases x with
    | error s => exact ⟨s, rfl⟩
    | ok _ => simp [lostReply] at hl
  have hk := tick_lost (tick_order h) he
  rw [keptAfter_core] at hk
  rw [kept_follows h, hk]
  exact ⟨t, rfl, fun ps hp => Nanodregg.Hosting.Proofs.Resident.decide_kept_first t hp⟩

/-- **Keybroker is unreliable**: a lost ask is never sent again before its ring is freed. -/
theorem broker_lost_spent : LostSpent .broker := by
  intro w m ess pre mid post e₁ e₂ r h hc hl h₁ h₂
  obtain ⟨q, x, rfl⟩ := req_broker h₁
  obtain ⟨q', x', rfl⟩ := req_broker h₂
  have hx : (askText x).isSome := by
    cases x <;> simp_all [lostReply, askText]
  exact bell_resident_conforms h hc hx

/-- **One Boolean per peer** (PROT-5): a reliable peer's lost reply leaves its request kept, to be
sent again; an unreliable peer's lost request is never sent again before its ring is freed. -/
theorem lost_reply_policy (p : Peer) :
    (p.reliable = true → LostKept p) ∧ (p.reliable = false → LostSpent p) := by
  cases p with
  | kernel => exact ⟨fun _ => kernel_lost_kept, fun h => by simp [Peer.reliable] at h⟩
  | broker => exact ⟨fun h => by simp [Peer.reliable] at h, fun _ => broker_lost_spent⟩

/-- **A lost ask keeps its obligation** (the deployed `lost_reply_keeps_obligation`): on every path
of a tick, an ask that ended `lost` is the tick's only ask, and the only answer the tick invokes is
`(unanswered WHY)` for that ring. Nothing is re-planned in its place: no second ask, no other text. -/
theorem lost_ask_keeps_obligation {w : Where} {m : Mem} {es : List Ev} {a : Tick} {r : Ring}
    {q : Broker.Ask} {why : String} (h : Hosting.Proofs.ResidentRun.Runs (tickP w m) es a)
    (hl : Ev.ask r q (.lost why) ∈ core es) :
    asks (core es) = [r] ∧
      ∀ r' t, (r', t) ∈ invokes (core es) → r' = r ∧ t = fit (named s!"unanswered {why}") := by
  obtain ⟨-, -, ha, hi⟩ := tick_counts h
  have hr := mem_asks hl
  rcases ha with ha | ⟨r₀, sh, y, p, x, pre, post, -, -, ha, hc⟩
  · rw [ha] at hr; cases hr
  · rw [ha] at hr
    obtain rfl : r = r₀ := by simpa using hr
    refine ⟨ha, fun r' t hm => ?_⟩
    -- the one ask event of the core is the lost one
    have hpre : asks pre = [] ∧ asks post = [] := by
      rw [hc] at ha; exact asks_one ha
    have hx : x = .lost why := by
      rw [hc] at hl
      simp only [List.mem_append, List.mem_cons] at hl
      rcases hl with hl | hl | hl | hl | hl
      · have := mem_asks hl; rw [hpre.1] at this; cases this
      · cases hl
      · cases hl
      · injection hl with _ _ h3; exact h3.symm
      · have := mem_asks hl; rw [hpre.2] at this; cases this
    subst hx
    rcases hi with hi | ⟨r₁, t₁, hi, ⟨-, -, -, -, -, ha'⟩ | ⟨sh₁, y₁, p₁, x₁, z, pre₁, post₁, -, -, ht, hc₁⟩⟩
    · rw [hi] at hm; cases hm
    · rw [ha] at ha'; cases ha'
    · rw [hi] at hm
      obtain ⟨rfl, rfl⟩ : r' = r₁ ∧ t = t₁ := by simpa using hm
      -- the ask of `hc₁` is the same lost ask
      have hpos : r' = r ∧ x₁ = .lost why := by
        have hm₁ : Ev.ask r' (Hosting.Resident.askOf w.conf r') x₁ ∈ core es := by
          rw [hc₁]; simp
        rw [hc] at hm₁
        simp only [List.mem_append, List.mem_cons] at hm₁
        rcases hm₁ with hm₁ | hm₁ | hm₁ | hm₁ | hm₁
        · have := mem_asks hm₁; rw [hpre.1] at this; cases this
        · cases hm₁
        · cases hm₁
        · injection hm₁ with h1 _ h3; exact ⟨h1, h3⟩
        · have := mem_asks hm₁; rw [hpre.2] at this; cases this
      obtain ⟨rfl, rfl⟩ := hpos
      simpa [askText] using ht.symm

end Resident

end Nanodregg.Lang.Contextual.Protocol.Failures
