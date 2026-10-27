/-
# Hosting.Proofs.Lifetime — one resident process's ticks: where its shape came from, and what it holds

`ResidentRun.Ticks w m ess`: the effects of one process's ticks, tick by tick (`ess.flatten` in
order): each tick a path of `tickP` (every result each effect could have) from the memory the tick
before went on with. `run` starts it at `{ shape := none, kept := seed }`, the seed being what the
volume held (`seedOf`). (HOSTING-48: the flattened twin `Lifetime` is deleted; `Ticks` is the one.)

- `tick_shape` / `tick_invoke_shape`: a tick hands on the shape it was given, or the one its own
  describe read; every invoke a tick sends is at the shape it was given or at the one its describe,
  sent first, read.
- `shape_provenance` (HOSTING-42 trigger (i)): in a lifetime that starts with no shape, every invoke
  `.cmd (.invoke sh r t) x` follows, earlier in the same process, a describe whose reply reads as
  `sh` (`describedShape`). The describe and the invoke may be ticks apart.
- `lifetime_bounds`: every ring and answer the resident invokes is within Lang's bounds (each ring
  read by `Lang.Read.readData` at the relation's row type, each answer text fitted, each seed read
  at `keptTy`), the premise `answer_args_at_answerArgTy` reads the strong form at.
-/
import Hosting.Proofs.ResidentRun
import Lang.Proofs.Read

namespace Nanodregg.Hosting.Proofs.Lifetime

open Nanodregg.Hosting Nanodregg.Hosting.Resident Nanodregg.Hosting.Proofs.ResidentRun

/-! ## The shape a tick hands on -/

theorem forgetThen_shape {n : Tick} {m' : Mem} {es : List Ev} (h : Runs (forgetThen n) es (.next m')) :
    n = .next m' := (forgetThen_next h).1

theorem useP_shape {m m' : Mem} {r : Ring} {n line : String} {p : List Ring} {gone : List ByteArray}
    {es : List Ev} (h : Runs (useP m r n line p gone) es (.next m')) : m'.shape = m.shape := by
  unfold useP at h
  split at h
  · cases h with | say h => have hn := forgetThen_shape h; cases hn; rfl
  · cases h with | say h => have hn := forgetThen_shape h; cases hn; rfl
  · cases h

theorem refusedP_shape {sh : Shape} {m m' : Mem} {r : Ring} {n line : String} {p : List Ring}
    {es : List Ev} (h : Runs (refusedP sh m r n line p) es (.next m')) : m'.shape = m.shape := by
  obtain ⟨pre, rest, rfl, -, hr⟩ := refusedP_path h
  rcases hr with ⟨c, y, s, why, rfl, -, hr⟩ | ⟨gone, hr⟩
  · obtain rfl := retry_next hr.symm; rfl
  · exact useP_shape hr

theorem deliver_shape {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (deliverP sh m r t) es (.next m')) : m'.shape = m.shape := by
  unfold deliverP at h
  split at h
  · cases h
  · cases h with
    | cmd x h =>
      rcases x with e | rr
      · simp only at h; cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
      · simp only at h
        split at h
        · cases h with
          | say h => have hn := forgetThen_shape h; cases hn; rfl
        · split at h
          · cases h with
            | cmd y h =>
              rcases y with e | rr'
              · simp only at h
                cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
              · simp only at h
                split at h
                · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
                · split at h
                  · cases h
                  · exact refusedP_shape h
          · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl

theorem answered_shape {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (answeredP sh m r t) es (.next m')) : m'.shape = m.shape := by
  unfold answeredP at h
  cases h with
  | say h =>
    cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
      · simp only [if_true] at h
        have hs := deliver_shape h
        exact hs

theorem actOn_shape {w : Where} {sh : Shape} {m m' : Mem} {p : List Ring} {es : List Ev}
    (h : Runs (actOn w sh m p) es (.next m')) : m'.shape = m.shape := by
  unfold actOn at h
  split at h
  · split at h
    · have hn := forgetThen_shape h; cases hn; rfl
    · cases h; rfl
  · exact deliver_shape h
  · cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        cases h with
        | ask x h =>
          rcases x with why | ans | why
          · simp only at h
            cases h with
            | say h => obtain rfl := retry_next (forgetThen_shape h); rfl
          · simp only at h
            have hs := answered_shape h
            exact hs
          · simp only at h
            cases h with
            | say h => have hs := answered_shape h; exact hs

theorem read_shape {w : Where} {sh : Shape} {m m' : Mem} {es : List Ev}
    (h : Runs (readP w sh m) es (.next m')) : m'.shape = m.shape := by
  unfold readP at h
  cases h with
  | cmd y h =>
    rcases y with e | rr
    · simp only at h; cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
    · simp only at h
      split at h
      · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
      · split at h
        · cases h
        · cases h with | hole h => exact actOn_shape (m := m.prune _) h

/-- **The shape a tick hands on** is the one it was given, or the one its own describe (its first
effect) read. -/
theorem tick_shape {w : Where} {m m' : Mem} {es : List Ev} (h : Runs (tickP w m) es (.next m')) :
    m'.shape = m.shape ∨ ∃ y rest, core es = .cmd .describe y :: rest ∧ describedShape w.conf y = m'.shape := by
  unfold tickP at h
  split at h
  · exact .inl (read_shape h)
  · rename_i hs
    cases h with
    | cmd y h =>
      rcases y with e | rr
      · simp only at h; cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; exact .inl rfl
      · simp only at h
        split at h
        · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; exact .inl rfl
        · rename_i hok
          split at h
          · rename_i sh hsh
            cases h with
            | say h =>
              have hs' := read_shape h
              have hx : rr.exit = Protocol.CommandExit.ok.code := Decidable.not_not.mp hok
              refine .inr ⟨.ok rr, _, core_cmd _ _ _, ?_⟩
              simp only [describedShape, hx, if_true, hsh, Except.toOption]
              exact hs'.symm
          · cases h

/-! ## The shape each invoke is sent at -/

theorem deliverAfter_mem {sh : Shape} {r : Ring} {x : Except String Reply} {rest : List Ev}
    (h : DeliverAfter sh r x rest) : ∀ e ∈ rest, (∃ b, e = .forget b) ∨ (∃ y, e = .cmd (.reread sh) y) ∨
      ∃ c y, e = .cmd (.probe c) y := by
  intro e he
  unfold DeliverAfter at h
  split at h
  · subst h; cases he
  · split at h
    · obtain ⟨b, rfl⟩ := h; simp at he; exact .inl ⟨b, he⟩
    · split at h
      · obtain ⟨y, rest', rfl, hr'⟩ := h
        rcases List.mem_cons.mp he with rfl | he
        · exact .inr (.inl ⟨y, rfl⟩)
        · split at hr'
          · rcases refusedCore_mem hr' e he with hb | hc
            · exact .inl hb
            · exact .inr (.inr hc)
          · subst hr'; cases he
      · subst h; cases he

theorem deliverCore_invoke {sh sh' : Shape} {r r' : Ring} {t t' : ByteArray} {x : Except String Reply}
    {es : List Ev} (h : DeliverCore sh r t es) (he : Ev.cmd (.invoke sh' r' t') x ∈ es) : sh' = sh := by
  obtain ⟨x₀, rest, rfl, hr⟩ := h
  rcases List.mem_cons.mp he with he | he
  · cases he; rfl
  · rcases deliverAfter_mem hr _ he with ⟨b, hb⟩ | ⟨y, hy⟩ | ⟨c, y, hy⟩
    · cases hb
    · cases hy
    · cases hy

theorem deliverCore_keep {sh : Shape} {r r' : Ring} {t t' : ByteArray} {b : Bool} {es : List Ev}
    (h : DeliverCore sh r t es) : Ev.keep r' t' b ∉ es := by
  obtain ⟨x₀, rest, rfl, hr⟩ := h
  intro he
  rcases List.mem_cons.mp he with he | he
  · cases he
  · rcases deliverAfter_mem hr _ he with ⟨b, hb⟩ | ⟨y, hy⟩ | ⟨c, y, hy⟩
    · cases hb
    · cases hy
    · cases hy

theorem readCore_invoke {c : Conf} {sh sh' : Shape} {k : Mem} {r : Ring}
    {t : ByteArray} {x : Except String Reply} {es : List Ev} (h : ReadCore c sh k es)
    (he : Ev.cmd (.invoke sh' r t) x ∈ es) : sh' = sh := by
  obtain ⟨y, rest, rfl, hr⟩ := h
  rcases List.mem_cons.mp he with he | he
  · cases he
  split at hr
  · subst hr; cases he
  · unfold ActCore at hr
    split at hr
    · rcases hr with ⟨-, b, rfl⟩ | ⟨-, rfl⟩ <;> simp at he
    · exact deliverCore_invoke hr he
    · rcases hr with rfl | ⟨x', rest', rfl, ha⟩
      · simp at he
      · simp only [List.mem_cons, reduceCtorEq, false_or] at he
        unfold AfterAsk at ha
        split at ha
        · obtain ⟨b, rfl⟩ := ha; simp at he
        · rcases ha with rfl | ⟨rest'', rfl, hd⟩
          · simp at he
          · simp only [List.mem_cons, reduceCtorEq, false_or] at he
            exact deliverCore_invoke hd he

/-- **Every invoke a tick sends is at the shape it was given, or at the one its describe read**
(the describe being the tick's first effect, the invoke after it). -/
theorem tick_invoke_shape {w : Where} {m : Mem} {es : List Ev} {a : Tick} (h : Runs (tickP w m) es a)
    {sh : Shape} {r : Ring} {t : ByteArray} {x : Except String Reply}
    (he : Ev.cmd (.invoke sh r t) x ∈ core es) :
    m.shape = some sh ∨ ∃ y rest, core es = .cmd .describe y :: rest ∧ describedShape w.conf y = some sh ∧
      Ev.cmd (.invoke sh r t) x ∈ rest := by
  have ho := tick_order h
  unfold TickCore at ho
  split at ho
  · rename_i sh₀ hs
    rw [readCore_invoke ho he]; exact .inl hs
  · obtain ⟨y, rest, hc, hr⟩ := ho
    rw [hc] at he
    rcases List.mem_cons.mp he with he' | he'
    · cases he'
    split at hr
    · subst hr; cases he'
    · rename_i sh₀ hsh
      have := readCore_invoke hr he'
      subst this
      exact .inr ⟨y, rest, hc, hsh, he'⟩

/-! ## Where an invoke's shape came from, across ticks -/

/-- **Trigger (i): an invoke's shape is a describe's reply, earlier in the same process.** In a
lifetime started with no shape (as `run` starts every one), every invoke `.cmd (.invoke sh r t) x`
is preceded, in the order the effects were performed, by a describe `y` whose reply reads as
exactly `sh`, maybe ticks earlier. -/
theorem shape_provenance {w : Where} :
    ∀ {m : Mem} {ess : List (List Ev)}, Ticks w m ess → ∀ {sh : Shape} {r : Ring} {t : ByteArray}
      {x : Except String Reply}, Ev.cmd (.invoke sh r t) x ∈ core ess.flatten →
      m.shape = some sh ∨ ∃ y pre mid post, core ess.flatten = pre ++ .cmd .describe y :: mid ++
        .cmd (.invoke sh r t) x :: post ∧ describedShape w.conf y = some sh := by
  intro m ess hl
  induction hl with
  | nil => intro sh r t x he; simp at he
  | last hr =>
    intro sh r t x he
    rcases tick_invoke_shape hr (by simpa using he) with hs | ⟨y, rest, hc, hy, hm⟩
    · exact .inl hs
    · obtain ⟨mid, post, rfl⟩ := List.append_of_mem hm
      exact .inr ⟨y, [], mid, post, by simp [hc], hy⟩
  | @next m₁ m' es₁ rest hr _ ih =>
    intro sh r t x he
    rw [List.flatten_cons, core_append] at he ⊢
    rcases List.mem_append.mp he with he | he
    · rcases tick_invoke_shape hr he with hs | ⟨y, rest₁, hc, hy, hm⟩
      · exact .inl hs
      · obtain ⟨mid, post, rfl⟩ := List.append_of_mem hm
        exact .inr ⟨y, [], mid, post ++ core rest.flatten, by rw [hc]; simp, hy⟩
    · rcases ih he with hs | ⟨y, pre, mid, post, hc, hy⟩
      · rcases tick_shape hr with hm | ⟨y, rest₁, hc₁, hy⟩
        · exact .inl (hm ▸ hs)
        · obtain ⟨a, b, hab⟩ := List.append_of_mem he
          exact .inr ⟨y, [], rest₁ ++ a, b, by rw [hc₁, hab]; simp, hy.trans hs⟩
      · exact .inr ⟨y, core es₁ ++ pre, mid, post, by rw [hc]; simp, hy⟩

/-! ## What the resident invokes is within Lang's bounds -/

/-- The decision `answer` is of the kept answer, exactly. -/
theorem decideTick_answer_kept {p : List Ring} {k : Option (Ring × ByteArray)} {r : Ring} {t : ByteArray}
    (h : decideTick p k = .answer r t) : k = some (r, t) := by
  unfold decideTick at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {p : List β}, l.mapM f = .ok p → ∀ y ∈ p, ∃ x ∈ l, f x = .ok y
  | [], p, h, y, hy => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; cases hy
  | a :: l, p, h, y, hy => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hfa : f a with
    | error e => rw [hfa] at h; cases h
    | ok b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., hfa⟩
        · obtain ⟨x, hx, hfx⟩ := mapM_ok_mem hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem mem_of_head {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => cases h
  | cons b l => simp at h; subst h; exact List.mem_cons_self ..

/-- A ring within Lang's bounds: what `Lang.Read.readData` reads at a pending row's type. -/
def RingOk (r : Ring) : Prop :=
  r.notBefore < Lang.Bounds.natLimit ∧ r.text.size ≤ Lang.Bounds.bytesMax ∧
    r.ringer.size ≤ Lang.Bounds.digestBytesMax ∧ Nanodregg.Hosting.Proofs.Resident.AimOk r.to

/-- A kept answer within Lang's bounds. -/
def KeptOk (k : Option (Ring × ByteArray)) : Prop :=
  ∀ r t, k = some (r, t) → RingOk r ∧ t.size ≤ Lang.Bounds.bytesMax

private theorem conforms_nat {n : Nat} {T : Lang.Ty} (h : Lang.Conforms (.nat n) T) : n < Lang.Bounds.natLimit := by
  cases h; assumption
private theorem conforms_bytes {s : ByteArray} {T : Lang.Ty} (h : Lang.Conforms (.bytes s) T) :
    s.size ≤ Lang.Bounds.bytesMax := by
  cases h; assumption
private theorem conforms_digest {s : ByteArray} {T : Lang.Ty} (h : Lang.Conforms (.digest s) T) :
    s.size ≤ Lang.Bounds.digestBytesMax := by
  cases h; assumption

private theorem readData_conforms {T : Lang.Ty} {s : String} {v : Lang.Data}
    (h : Lang.Read.readData T s = .ok v) : Lang.Conforms v T := by
  unfold Lang.Read.readData at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · exact Lang.Read.dataAt_conforms _ _ _ h

theorem rowConforms_mem : ∀ {ds : List (Lang.Label × Lang.Data)} {r : List (Lang.Label × Lang.Ty)},
    Lang.RowConforms ds r → ∀ p ∈ ds, ∃ A, Lang.Conforms p.2 A
  | [], _, _, p, hp => by cases hp
  | _ :: _, _, .cons hd hr, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, hd⟩
    · exact rowConforms_mem hr p hp

theorem conforms_record_mem {ds : List (Lang.Label × Lang.Data)} {T : Lang.Ty}
    (h : Lang.Conforms (.record ds) T) : ∀ p ∈ ds, ∃ A, Lang.Conforms p.2 A := by
  cases h with
  | record hr => exact rowConforms_mem hr

theorem conforms_inj {ℓ : Lang.Label} {d : Lang.Data} {T : Lang.Ty} (h : Lang.Conforms (.inj ℓ d) T) :
    ∃ A, Lang.Conforms d A := by
  cases h with
  | inj _ h => exact ⟨_, h⟩

/-- An aim's record conforming to any type is within bounds. -/
private theorem aimOk_of_conforms {c o v : ByteArray} {m : Nat} {T : Lang.Ty}
    (h : Lang.Conforms (.record [("cand", .digest c), ("method", .nat m), ("target", .digest o), ("via", .digest v)]) T) :
    Nanodregg.Hosting.Proofs.Resident.AimOk (some ⟨c, m, o, v⟩) := by
  obtain ⟨Ac, hc⟩ := conforms_record_mem h _ (List.mem_cons_self ..)
  obtain ⟨Am, hm⟩ := conforms_record_mem h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨Ao, ho⟩ := conforms_record_mem h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨Av, hv⟩ := conforms_record_mem h _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  intro a ha
  cases ha
  exact ⟨conforms_digest hc, conforms_nat hm, conforms_digest ho, conforms_digest hv⟩

private theorem aimOk_none : Nanodregg.Hosting.Proofs.Resident.AimOk none := fun _ h => by cases h

/-- A ring the resident reads is within bounds: `Ring.read` is `readData` at the row type. -/
theorem ring_read_ok {sh : Shape} {line : String} {r : Ring} (h : Ring.read sh line = .ok r) : RingOk r := by
  unfold Ring.read at h
  split at h
  · rename_i v hv
    have hc := readData_conforms hv
    unfold Ring.ofRow at h
    split at h
    · rename_i g n t
      cases h
      obtain ⟨Ak, hk⟩ := conforms_record_mem hc _ (List.mem_cons_self ..)
      obtain ⟨Av, hv'⟩ := conforms_record_mem hc _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨Ag, hg⟩ := conforms_record_mem hk _ (List.mem_cons_self ..)
      obtain ⟨An, hn⟩ := conforms_record_mem hk _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨Ac, hcap⟩ := conforms_record_mem hv' _ (List.mem_cons_self ..)
      obtain ⟨Aa, ha⟩ := conforms_inj hcap
      obtain ⟨Ax, hx⟩ := conforms_record_mem ha _ (List.mem_cons_self ..)
      exact ⟨conforms_nat hn, conforms_bytes hx, conforms_digest hg, aimOk_none⟩
    · rename_i g n t c m o v
      cases h
      obtain ⟨Ak, hk⟩ := conforms_record_mem hc _ (List.mem_cons_self ..)
      obtain ⟨Av, hv'⟩ := conforms_record_mem hc _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨Ag, hg⟩ := conforms_record_mem hk _ (List.mem_cons_self ..)
      obtain ⟨An, hn⟩ := conforms_record_mem hk _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨Ac, hcap⟩ := conforms_record_mem hv' _ (List.mem_cons_self ..)
      obtain ⟨Aa, ha⟩ := conforms_inj hcap
      obtain ⟨Ax, hx⟩ := conforms_record_mem ha _ (List.mem_cons_self ..)
      obtain ⟨At, hto⟩ := conforms_record_mem ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨Aai, hai⟩ := conforms_inj hto
      exact ⟨conforms_nat hn, conforms_bytes hx, conforms_digest hg, aimOk_of_conforms hai⟩
    · cases h
  · cases h

theorem readRings_ok {sh : Shape} {y : Except String Reply} {p : List Ring} (h : readRings sh y = some p) :
    ∀ r ∈ p, RingOk r := by
  intro r hr
  unfold readRings at h
  split at h
  · split at h
    · rename_i rr _
      cases ha : readOut sh rr with
      | error e => rw [ha] at h; cases h
      | ok p' =>
        rw [ha] at h
        cases h
        unfold readOut at ha
        split at ha
        · cases ha
        · rename_i out _
          cases hb : Ring.readAll sh out with
          | error e => rw [hb] at ha; cases ha
          | ok q =>
            rw [hb] at ha
            simp only [Except.mapError, Except.ok.injEq] at ha
            subst ha
            unfold Ring.readAll at hb
            obtain ⟨line, -, hl⟩ := mapM_ok_mem hb r hr
            exact ring_read_ok hl
    · cases h
  · cases h

theorem textMax_bytes {t : ByteArray} (h : t.size ≤ textMax) : t.size ≤ Lang.Bounds.bytesMax :=
  Nat.le_trans h Nanodregg.Hosting.Proofs.Resident.textMax_le_bytesMax

theorem askText_ok {x : AskEnd} {t : ByteArray} (h : askText x = some t) : t.size ≤ Lang.Bounds.bytesMax := by
  unfold askText at h
  split at h
  · cases h
  · cases h; exact textMax_bytes (Nanodregg.Hosting.Proofs.Resident.answerText_size _).2
  · cases h; exact textMax_bytes (Nanodregg.Hosting.Proofs.Resident.fit_size _).2

/-- **Every answer a tick keeps is within bounds**: its ring is one the tick's read returned, its
text the intent or what the ask ended with, each fitted. -/
theorem tick_keeps_ok {w : Where} {m : Mem} {es : List Ev} {a : Tick} (h : Runs (tickP w m) es a)
    {r : Ring} {t : ByteArray} {b : Bool} (he : Ev.keep r t b ∈ core es) :
    RingOk r ∧ t.size ≤ Lang.Bounds.bytesMax := by
  have read_keep : ∀ {sh k es}, ReadCore w.conf sh k es → Ev.keep r t b ∈ es →
      RingOk r ∧ t.size ≤ Lang.Bounds.bytesMax := by
    intro sh k es hr he
    obtain ⟨y, rest, rfl, hr⟩ := hr
    rcases List.mem_cons.mp he with he | he
    · cases he
    split at hr
    · subst hr; cases he
    · rename_i p hp
      unfold ActCore at hr
      split at hr
      · rcases hr with ⟨-, b, rfl⟩ | ⟨-, rfl⟩ <;> simp at he
      · exact absurd he (deliverCore_keep hr)
      · rename_i r₀ hd
        have hr₀ : RingOk r₀ := readRings_ok hp r₀
          (List.mem_filter.mp (mem_of_head (ask_is_head hd).1)).1
        have hint : intentText.size ≤ Lang.Bounds.bytesMax :=
          textMax_bytes (Nanodregg.Hosting.Proofs.Resident.fit_size _).2
        rcases hr with rfl | ⟨x', rest', rfl, ha⟩
        · simp at he; obtain ⟨rfl, rfl, -⟩ := he; exact ⟨hr₀, hint⟩
        · rcases List.mem_cons.mp he with he | he
          · cases he; exact ⟨hr₀, hint⟩
          rcases List.mem_cons.mp he with he | he
          · cases he
          unfold AfterAsk at ha
          split at ha
          · obtain ⟨b, rfl⟩ := ha; simp at he
          · rename_i t' ht'
            rcases ha with rfl | ⟨rest'', rfl, hd'⟩
            · simp at he; obtain ⟨rfl, rfl, -⟩ := he; exact ⟨hr₀, askText_ok ht'⟩
            · rcases List.mem_cons.mp he with he | he
              · cases he; exact ⟨hr₀, askText_ok ht'⟩
              · exact absurd he (deliverCore_keep hd')
  have ho := tick_order h
  unfold TickCore at ho
  split at ho
  · exact read_keep ho he
  · obtain ⟨y, rest, hc, hr⟩ := ho
    rw [hc] at he
    rcases List.mem_cons.mp he with he | he
    · cases he
    split at hr
    · subst hr; cases he
    · exact read_keep hr he

theorem keptAfter_ok : ∀ {es : List Ev} {k : Option (Ring × ByteArray)}, KeptOk k →
    (∀ r t, Ev.keep r t true ∈ es → RingOk r ∧ t.size ≤ Lang.Bounds.bytesMax) → KeptOk (keptAfter k es)
  | [], _, hk, _ => hk
  | .keep r t true :: es, _, _, he =>
    keptAfter_ok (es := es) (k := some (r, t))
      (fun r' t' h => by cases h; exact he r t (List.mem_cons_self ..))
      (fun r t h => he r t (List.mem_cons_of_mem _ h))
  | .keep _ _ false :: es, k, hk, he =>
    keptAfter_ok (es := es) (k := k) hk (fun r t h => he r t (List.mem_cons_of_mem _ h))
  | .forget true :: es, _, _, he =>
    keptAfter_ok (es := es) (k := none) (fun _ _ h => by cases h) (fun r t h => he r t (List.mem_cons_of_mem _ h))
  | .forget false :: es, k, hk, he =>
    keptAfter_ok (es := es) (k := k) hk (fun r t h => he r t (List.mem_cons_of_mem _ h))
  | .cmd _ _ :: es, k, hk, he =>
    keptAfter_ok (es := es) (k := k) hk (fun r t h => he r t (List.mem_cons_of_mem _ h))
  | .ask _ _ _ :: es, k, hk, he =>
    keptAfter_ok (es := es) (k := k) hk (fun r t h => he r t (List.mem_cons_of_mem _ h))
  | .say _ :: es, k, hk, he =>
    keptAfter_ok (es := es) (k := k) hk (fun r t h => he r t (List.mem_cons_of_mem _ h))

theorem mem_core_keep {r : Ring} {t : ByteArray} {b : Bool} {es : List Ev} (h : Ev.keep r t b ∈ es) :
    Ev.keep r t b ∈ core es := by
  simp only [core, List.mem_filter]; exact ⟨h, rfl⟩

/-- **What a tick invokes is within bounds**, when the answer it was handed is. -/
theorem tick_invoke_ok {w : Where} {m : Mem} {es : List Ev} {a : Tick} (h : Runs (tickP w m) es a)
    (hk : KeptOk m.kept) {sh : Shape} {r : Ring} {t : ByteArray} {x : Except String Reply}
    (he : Ev.cmd (.invoke sh r t) x ∈ core es) : RingOk r ∧ t.size ≤ Lang.Bounds.bytesMax := by
  obtain ⟨-, -, -, hinv⟩ := tick_counts h
  have hmem : (r, t) ∈ invokes (core es) := List.mem_filterMap.mpr ⟨_, he, rfl⟩
  rcases hinv with hn | ⟨r', t', hrt, hc⟩
  · rw [hn] at hmem; cases hmem
  · rw [hrt, List.mem_singleton] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    rcases hc with ⟨_, _, _, _, hd, _⟩ | ⟨_, _, _, _, _, pre, post, _, _, _, hc⟩
    · exact hk _ _ (decideTick_answer_kept hd)
    · exact tick_keeps_ok h (b := true) (by rw [hc]; simp)

/-- **Every ring and answer the resident invokes, in a whole lifetime, is within Lang's bounds**,
when the seed it started with is (`seed_ok`: what `run` reads back from the volume is). -/
theorem lifetime_bounds {w : Where} :
    ∀ {m : Mem} {ess : List (List Ev)}, Ticks w m ess → KeptOk m.kept → ∀ {sh : Shape} {r : Ring}
      {t : ByteArray} {x : Except String Reply}, Ev.cmd (.invoke sh r t) x ∈ core ess.flatten →
      RingOk r ∧ t.size ≤ Lang.Bounds.bytesMax := by
  intro m ess hl
  induction hl with
  | nil => intro hk sh r t x he; simp at he
  | last hr => intro hk sh r t x he; exact tick_invoke_ok hr hk (by simpa using he)
  | @next m₁ m' es₁ rest hr _ ih =>
    intro hk sh r t x he
    rw [List.flatten_cons, core_append] at he
    rcases List.mem_append.mp he with he | he
    · exact tick_invoke_ok hr hk he
    · refine ih ?_ he
      rw [kept_follows hr]
      exact keptAfter_ok hk (fun r t h => tick_keeps_ok hr (mem_core_keep h))

/-- What `run` reads back from the volume is within bounds: `keptRead` is `readData` at `keptTy`. -/
theorem seed_ok {held : Option (Option String)} {k : Option (Ring × ByteArray)} (h : seedOf held = some k) :
    KeptOk k := by
  intro r t hk
  subst hk
  unfold seedOf at h
  split at h
  · cases h
  · cases h
  · rename_i s
    cases hs : keptRead s with
    | none => rw [hs] at h; cases h
    | some q =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      cases h
      unfold keptRead at hs
      split at hs
      · rename_i tt n g x hv
        cases hs
        have hc := readData_conforms hv
        cases hc with
        | record hrow =>
          cases hrow with
          | cons ht hrow =>
            cases hrow with
            | cons hn hrow =>
              cases hrow with
              | cons hg hrow =>
                cases hrow with
                | cons hx _ =>
                  exact ⟨⟨conforms_nat hn, conforms_bytes hx, conforms_digest hg, aimOk_none⟩, conforms_bytes ht⟩
      · rename_i tt n g x c m o v hv
        cases hs
        have hc := readData_conforms hv
        cases hc with
        | record hrow =>
          cases hrow with
          | cons ht hrow =>
            cases hrow with
            | cons hn hrow =>
              cases hrow with
              | cons hg hrow =>
                cases hrow with
                | cons hx hrow =>
                  cases hrow with
                  | cons hto _ =>
                    obtain ⟨Aai, hai⟩ := conforms_inj hto
                    exact ⟨⟨conforms_nat hn, conforms_bytes hx, conforms_digest hg, aimOk_of_conforms hai⟩, conforms_bytes ht⟩
      · cases hs

end Nanodregg.Hosting.Proofs.Lifetime
