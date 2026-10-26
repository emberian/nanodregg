/-
# Hosting.Proofs.SocketStrong — the member socket, strong form: the delivered answer IS the resident's datum

`Socket.delivered_answer_committed` says an `ok` answer is a committed call carrying the TEXT the
resident printed, read at whatever type the bell's method declares on follow's World. This module
joins that text to the type the resident checked, `answerArgTy`, so the call's argument bytes are
`answerDatum r t`'s (R-0065), under the same `StdioLeg` premise and nothing more. The three facts
HOSTING-42 named as its triggers, each a theorem here or below:

- (i) `Lifetime.shape_provenance`: the shape an invoke is sent at was read, earlier in the same
  process, from a describe's reply.
- (ii) `reach_packageAt` (`Protocol.Command.step_packageAt`, KERNEL-64's `submit_object_head`, the ROM
  rule of `Lang.readPackage`): follow's World keeps the bell's package and the package's cell across
  every frame it answers.
- (iii) `describe_shape`: a description that reads as a shape says the bell's method `answer` has
  argument type exactly `answerArgTy` (`describe`'s `noBreak` and kind check, `methodLine`'s
  `labelAtom` and `Ty.wf`, `Lang.Print.readTy_ty`), and that the package is the Bell
  (`describeText_core`, `bellCore_ok`: the `core` line is the package cell's bytes, HOSTING-45).

`delivered_answer_committed_strong` assembles them with `run_describe_ok` (a describe that ends ok
is follow's own description, on the World its `done` was handed out at) and `StdioLeg`'s one
follower (`legFrom_suffix`: the invoke's run starts at a World follow reached from the describe's).
-/
import Hosting.Proofs.Socket
import Protocol.Proofs.FollowHead
import Protocol.Proofs.Describe
import Lang.Proofs.Load

namespace Nanodregg.Hosting.Proofs.Socket

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Follow keeps an object's package and the package's ROM cell, across every frame** (HOSTING-42
trigger (ii), `Protocol.Command.step_packageAt`). -/
theorem reach_packageAt [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {dc : Codec.Stream D}
    {B : Thin.Base (World D)} {me : Self D} {obj P : D} {pc : Cell} {w w' : World D}
    (h : Reach X dc B me w w') (hp : PackageAt X w obj P pc) : PackageAt X w' obj P pc := by
  obtain ⟨S, h⟩ := h
  induction h with
  | refl => exact hp
  | tail _ hm ih =>
    obtain ⟨f, f', kb, p, r, rfl, hs, rfl⟩ := hm
    exact step_packageAt hs (ih hp)

/-! ## The describe: what a description that reads as a shape says (HOSTING-42 trigger (iii)) -/

omit [Ord D] [DecidableEq D] in
/-- The resident's describe argv, as follow parses it: `read` of the object the config's `bell`
names, `?`. -/
theorem describeArgv_parse {X : Ctx D} {c : Resident.Conf} {cmd : Command.Cmd D}
    (h : Command.parse X.digestOf (Resident.describeArgv c) = .ok cmd) :
    ∃ o, X.digestOf c.bell = some o ∧ cmd = .describe o := by
  unfold Command.parse Resident.describeArgv Resident.hexOf at h
  split at h
  · cases h
  have hv : Verb.ofWord? "read" = some .read := by decide
  simp only [List.zipIdx, mapEx, fromUTF8_toUTF8', hv, bind, Except.bind, pure, Except.pure] at h
  simp only [parseVerb, digestArg, ofHex_hex] at h
  cases hb : X.digestOf c.bell <;>
    simp [hb, Option.bind, bind, Except.map, Functor.map] at h
  exact ⟨_, rfl, h.symm⟩

/-- **A describe ends `ok` only at follow's own description of the object**, on the World the step
left follow at. -/
theorem step_describe_ok {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result o e : ByteArray} {st : State}
    (hst : State.ofBytes kb = some st) (h4 : st.phase ≠ 4)
    (hd : ∀ cmd, Command.parse X.digestOf st.argv = .ok cmd → ∃ obj, cmd = .describe obj)
    (h : Command.step X dc B me f kb result = (f', p, .done CommandExit.ok.code.toUInt8 o e)) :
    ∃ obj, Command.parse X.digestOf st.argv = .ok (.describe obj) ∧
      describe X f'.world obj = .done CommandExit.ok.code.toUInt8 o e := by
  obtain ⟨argv, phase, acc⟩ := st
  unfold Command.step at h
  simp only [hst, Option.map_some, Option.getD_some] at h
  split at h
  · rename_i hs; cases hs
  · simp [refused, CommandExit.code] at h
  rename_i st cmd hs hp
  simp only [Option.some.injEq] at hs
  subst hs
  repeat' split at h
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (try (obtain ⟨rfl, -, h⟩ := h))
  all_goals (try (exfalso; obtain ⟨_, hc⟩ := hd _ hp; cases hc; done))
  all_goals (try contradiction)
  all_goals (try (simp [refused, behind, CommandExit.code] at h; done))
  all_goals (try (exact absurd h refusedAt_ne_ok))
  all_goals (try (exact absurd h custodyEnd_ne_ok))
  all_goals (try (exact absurd h envelopeRefused_ne_ok))
  all_goals (try (exact absurd h (next_ne_ok (fun _ => rfl))))
  all_goals (try (exact absurd h (next_ne_ok (fun _ => envelopeSign_cont))))
  all_goals exact ⟨_, hp, h⟩

/-- **A run of a describe that ends `ok` is follow's description**, at the World its `done` was
handed out at. -/
theorem run_describe_ok {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {w₀ : World D} {argv : List ByteArray}
    (hd : ∀ cmd, Command.parse X.digestOf argv = .ok cmd → ∃ obj, cmd = .describe obj) :
    ∀ {f : Follow D} {r : Command.Reply} {fe : Follow D} {fin : UInt8 × ByteArray × ByteArray},
      FollowRun X dc B me f r fe fin → ContOf X dc B me w₀ argv r →
      Reach X dc B me w₀ f.world → (∀ o e, r ≠ .done CommandExit.ok.code.toUInt8 o e) →
      fin.1 = CommandExit.ok.code.toUInt8 →
      ∃ obj, Command.parse X.digestOf argv = .ok (.describe obj) ∧
        describe X fe.world obj = .done CommandExit.ok.code.toUInt8 fin.2.1 fin.2.2 := by
  intro f r fe fin hrun
  induction hrun with
  | done =>
    intro _ _ hnd he
    exact absurd (by simp only at he; rw [he]) (hnd _ _)
  | @step f g f' fe r r' k res p fin hk hg hs rest ih =>
    intro hc hw hnd he
    have hwg := hw.trans hg
    by_cases hdn : ∃ o e, r' = .done CommandExit.ok.code.toUInt8 o e
    · obtain ⟨o, e, rfl⟩ := hdn
      cases rest with
      | step hk' _ _ _ => simp [Command.Reply.cont] at hk'
      | done =>
      cases hst : State.ofBytes k with
      | none => have := step_bad hs hst; simp [refused, CommandExit.code] at this
      | some st =>
        obtain ⟨harg, hpl⟩ := hc k st hk hst
        have h4 : st.phase ≠ 4 := by
          intro h4
          obtain ⟨_, _, cmd, s, rs, b, u, sig, hpc, hb, -⟩ := hpl h4
          obtain ⟨obj, rfl⟩ := hd _ hpc
          simp [Command.body] at hb
        obtain ⟨obj, hp, hdesc⟩ := step_describe_ok hst h4 (harg ▸ hd) hs
        exact ⟨obj, harg ▸ hp, hdesc⟩
    · exact ih (contOf_step hc hk hwg hs) (hwg.step hs) (fun o e h => hdn ⟨o, e, h⟩) he

/-! ### A description's lines, read back -/

omit [Ord D] [DecidableEq D] in
theorem splitLines_line {l : List Char} (hl : ∀ c ∈ l, c ≠ '\n') (rest : List Char) :
    Resident.splitLines (l ++ '\n' :: rest) = l :: Resident.splitLines rest := by
  induction l with
  | nil => simp [Resident.splitLines]
  | cons c l ih =>
    have hc : c ≠ '\n' := hl c (List.mem_cons_self ..)
    rw [List.cons_append, Resident.splitLines, if_neg hc, ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]

omit [Ord D] [DecidableEq D] in
theorem splitLines_join : ∀ (ls : List String), (∀ l ∈ ls, noBreak l = true) →
    Resident.splitLines (String.join (ls.map (· ++ "\n"))).toList = ls.map String.toList ++ [[]]
  | [], _ => by simp [Resident.splitLines]
  | l :: ls, h => by
    have hl : ∀ c ∈ l.toList, c ≠ '\n' := by
      have := h l (List.mem_cons_self ..)
      simp only [noBreak, Bool.not_eq_true'] at this
      intro c hc he; subst he
      simp [hc] at this
    have ih := splitLines_join ls (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp at ih ⊢
    rw [splitLines_line hl, ih]

omit [Ord D] [DecidableEq D] in
theorem digits_noSpace (n : Nat) : ∀ c ∈ (toString n).toList, c ≠ ' ' := by
  intro c hc h
  subst h
  simp [toString, Nat.repr] at hc
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp at this

omit [Ord D] [DecidableEq D] in
theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by simp at h; subst h; cases hy
  | a :: l, r, h, y, hy => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., hfa⟩
        · obtain ⟨x, hx, hfx⟩ := mapM_some_mem hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

omit [Ord D] [DecidableEq D] in
/-- A package's description lines: the only ones in `method` form are its methods' lines. -/
theorem packageLines_method {pk : Lang.Package} {ls : List String} (h : packageLines (D := D) pk = some ls)
    {l : String} (hl : l ∈ ls) {i lab ty : String} (hm : Resident.methodWords l.toList = some (i, lab, ty)) :
    ∃ j ℓ sg a, Lang.resolveMethod (D := D) pk j = .ok (ℓ, sg) ∧ Lang.labelAtom ℓ = true ∧
      sg.arg.wf = true ∧ Lang.Print.ty sg.arg = some a ∧ l = s!"method {j} {ℓ} {a}" := by
  unfold packageLines at h
  cases hst : Lang.Print.ty pk.state with
  | none => simp [hst] at h
  | some st =>
    cases hms : (List.range pk.methods.length).mapM (methodLine (D := D) pk) with
    | none => simp [hst, hms] at h
    | some ms =>
      cases hrs : pk.rels.mapM relLine with
      | none => simp [hst, hms, hrs] at h
      | some rs =>
        simp only [hst, hms, hrs, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [List.mem_append, List.mem_cons] at hl
        rcases hl with ((hl | hl | hl) | hl) | hl
        · unfold docLines at hl
          split at hl
          · cases hl
          · simp at hl; subst hl; simp [toString, Resident.methodWords] at hm
        · subst hl; simp [toString, Resident.methodWords] at hm
        · obtain ⟨mj, hmj, hl⟩ := List.mem_flatten.mp hl
          obtain ⟨j, -, hj⟩ := mapM_some_mem hms mj hmj
          obtain ⟨ℓ, sg, a, cs, hr, hat, hwf, ha, hc, rfl⟩ := methodLine_resolves hj
          rcases List.mem_cons.mp hl with rfl | hl
          · exact ⟨j, ℓ, sg, a, hr, hat, hwf, ha, rfl⟩
          · unfold callLines at hc
            obtain ⟨⟨k, jj⟩, -, hk⟩ := mapM_some_mem hc l hl
            obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hk
            simp [toString, Resident.methodWords] at hm
        · obtain ⟨ℓ, -, rfl⟩ := List.mem_map.mp hl
          simp [toString, Resident.methodWords] at hm
        · obtain ⟨r, -, hr⟩ := mapM_some_mem hrs l hl
          unfold relLine at hr
          obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hr
          simp [toString, Resident.methodWords] at hm

theorem describeText_method {X : Ctx D} {w : World D} {obj : D} {cell : Cell} {ls : List String}
    (h : describeText X w obj cell = .ok ls) {l : String} (hl : l ∈ ls) {i lab ty : String}
    (hm : Resident.methodWords l.toList = some (i, lab, ty)) :
    ∃ P pk j ℓ sg a, packageOf X obj cell = .ok (some P) ∧
      Lang.readPackage (worldLook X.env w) P = .ok pk ∧ Lang.resolveMethod (D := D) pk j = .ok (ℓ, sg) ∧
      Lang.labelAtom ℓ = true ∧ sg.arg.wf = true ∧ Lang.Print.ty sg.arg = some a ∧
      l = s!"method {j} {ℓ} {a}" := by
  unfold describeText at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i v hv
  cases h
  rcases List.mem_cons.mp hl with rfl | hl
  · simp [toString, Resident.methodWords] at hm
  rcases List.mem_append.mp hl with hl | hl
  · cases ho : cell.slots.get slotOwner with
    | none => simp [ho] at hl
    | some ow =>
      simp [ho] at hl
      subst hl
      simp [toString, Resident.methodWords] at hm
  unfold describeLines at hv
  simp only [bind, Except.bind, pure, Except.pure] at hv
  cases hp : packageOf X obj cell with
  | error e => simp [hp, Except.mapError] at hv
  | ok pkg =>
  cases hlw : lawsOf X obj cell with
  | error e => simp [hp, hlw, Except.mapError] at hv
  | ok laws =>
  simp only [hp, hlw, Except.mapError] at hv
  cases pkg with
  | none =>
    simp only at hv
    split at hv
    · cases hv
    · rename_i r hr
      cases hv
      rcases List.mem_append.mp hl with hl | hl
      · simp only [List.mem_singleton] at hl
        subst hl
        simp [Resident.methodWords] at hm
      · obtain ⟨x, -, hx⟩ := Lifetime.mapM_ok_mem hr l hl
        repeat' split at hx
        all_goals first | (cases hx; done) | skip
        cases hx
        simp [toString, Resident.methodWords] at hm
  | some P =>
    simp only at hv
    split at hv
    · cases hv
    · rename_i pk hpk
      split at hv
      · rename_i pls hpls
        split at hv
        · cases hv
        · rename_i r hr
          cases hv
          have hrp : Lang.readPackage (worldLook X.env w) P = .ok pk := by
            split at hpk
            · cases hpk
            · cases hpk; assumption
          rcases List.mem_cons.mp hl with rfl | hl
          · simp [toString, Resident.methodWords] at hm
          rcases List.mem_cons.mp hl with rfl | hl
          · simp [toString, Resident.methodWords] at hm
          rcases List.mem_append.mp hl with hl | hl
          · obtain ⟨j, ℓ, sg, a, hr', hat, hwf, ha, rfl⟩ := packageLines_method hpls hl hm
            exact ⟨P, pk, j, ℓ, sg, a, rfl, hrp, hr', hat, hwf, ha, rfl⟩
          · obtain ⟨x, -, hx⟩ := Lifetime.mapM_ok_mem hr l hl
            repeat' split at hx
            all_goals first | (cases hx; done) | skip
            cases hx
            simp [toString, Resident.methodWords] at hm
      · cases hv
omit [Ord D] [DecidableEq D] in
/-- A package's description lines: none is in `core` form. -/
theorem packageLines_core {pk : Lang.Package} {ls : List String} (h : packageLines (D := D) pk = some ls)
    {l : String} (hl : l ∈ ls) : Resident.coreWords l.toList = none := by
  unfold packageLines at h
  cases hst : Lang.Print.ty pk.state with
  | none => simp [hst] at h
  | some st =>
    cases hms : (List.range pk.methods.length).mapM (methodLine (D := D) pk) with
    | none => simp [hst, hms] at h
    | some ms =>
      cases hrs : pk.rels.mapM relLine with
      | none => simp [hst, hms, hrs] at h
      | some rs =>
        simp only [hst, hms, hrs, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [List.mem_append, List.mem_cons] at hl
        rcases hl with ((hl | hl | hl) | hl) | hl
        · unfold docLines at hl
          split at hl
          · cases hl
          · simp at hl; subst hl; simp [toString, Resident.coreWords]
        · subst hl; simp [toString, Resident.coreWords]
        · obtain ⟨mj, hmj, hl⟩ := List.mem_flatten.mp hl
          obtain ⟨j, -, hj⟩ := mapM_some_mem hms mj hmj
          obtain ⟨ℓ, sg, a, cs, -, -, -, -, hc, rfl⟩ := methodLine_resolves hj
          rcases List.mem_cons.mp hl with rfl | hl
          · simp [toString, Resident.coreWords]
          · unfold callLines at hc
            obtain ⟨⟨k, jj⟩, -, hk⟩ := mapM_some_mem hc l hl
            obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hk
            simp [toString, Resident.coreWords]
        · obtain ⟨ℓ, -, rfl⟩ := List.mem_map.mp hl
          simp [toString, Resident.coreWords]
        · obtain ⟨r, -, hr⟩ := mapM_some_mem hrs l hl
          unfold relLine at hr
          obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hr
          simp [toString, Resident.coreWords]

omit [Ord D] [DecidableEq D] in
theorem word_append {ys : List Char} : ∀ {xs : List Char}, (∀ c ∈ xs, c ≠ ' ') →
    Resident.word (xs ++ ' ' :: ys) = some (xs, ys)
  | [], _ => by simp [Resident.word]
  | x :: xs, h => by
    have hx := h x (List.mem_cons_self ..)
    have ih := word_append (ys := ys) (xs := xs) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp [Resident.word, hx, ih]

omit [Ord D] [DecidableEq D] in
theorem atom_noSpace {l : String} (h : Lang.labelAtom l = true) : ∀ c ∈ l.toList, c ≠ ' ' := by
  intro c hc hh
  subst hh
  unfold Lang.labelAtom at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 _ hc
  revert this; decide

omit [Ord D] [DecidableEq D] in
/-- A method line's words are its index, its label and its type text. -/
theorem methodWords_line (i : Nat) {l : String} (a : String) (hl : Lang.labelAtom l = true) :
    Resident.methodWords (s!"method {i} {l} {a}").toList = some (toString i, l, a) := by
  have key : ∀ (s : String), (∀ c ∈ s.toList, c ≠ ' ') →
      Resident.methodWords ("method " ++ s ++ " " ++ l ++ " " ++ a).toList = some (s, l, a) := by
    intro s hs
    have h1 := word_append (ys := l.toList ++ ' ' :: a.toList) hs
    have h2 := word_append (ys := a.toList) (atom_noSpace hl)
    simp [Resident.methodWords, h1, h2]
  exact key _ (digits_noSpace i)


omit [Ord D] [DecidableEq D] in
theorem answerWords_some {ls : List (List Char)} {i ty : String} (h : Resident.answerWords ls = some (i, ty)) :
    ∃ l ∈ ls, Resident.methodWords l = some (i, "answer", ty) := by
  unfold Resident.answerWords at h
  obtain ⟨l, hl, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · rename_i i' ty' hmw; cases hf; exact ⟨l, hl, hmw⟩
  · cases hf

omit [Ord D] [DecidableEq D] in
/-- What a shape the resident read says of the text it read: the package's `core` line passed
`bellCore` (HOSTING-45), the first `method I answer TYPE` line's index is the shape's, and its type
text reads as `answerArgTy`. -/
theorem shape_read_ok {out : String} {sh : Resident.Shape} (h : Resident.Shape.read out = .ok sh) :
    (∃ p, Resident.bellCore (Resident.splitLines out.toList) = .ok p) ∧
    ∃ i ty, Resident.answerWords (Resident.splitLines out.toList) = some (i, ty) ∧
      i.toNat? = some sh.answer ∧ Lang.Read.readTy ty = .ok Resident.answerArgTy := by
  unfold Resident.Shape.read at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i p hp
  refine ⟨⟨p, hp⟩, ?_⟩
  unfold Resident.Shape.ofLines at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rename_i i ty haw _ j hj _ T hT hTa _ d _ _ _ _
  cases h
  exact ⟨i, ty, haw, hj, hTa ▸ hT⟩

theorem describe_ok_text {X : Ctx D} {w : World D} {obj : D} {o e : ByteArray}
    (h : describe X w obj = .done CommandExit.ok.code.toUInt8 o e) :
    ∃ cell ls, w.live X.env obj = some cell ∧ cell.kind = kindObject ∧ describeText X w obj cell = .ok ls ∧
      (∀ l ∈ ls, noBreak l = true) ∧ o = (String.join (ls.map (· ++ "\n"))).toUTF8 := by
  unfold describe at h
  split at h
  · simp [refused, CommandExit.code] at h
  · rename_i cell hl
    split at h
    · simp [refused, CommandExit.code] at h
    · rename_i hk
      split at h
      · rename_i ls ht
        split at h
        · rename_i hall
          simp only [printed, Command.Reply.done.injEq] at h
          exact ⟨cell, ls, hl, Decidable.not_not.mp hk, ht, List.all_eq_true.mp hall, h.2.1.symm⟩
        · simp [refused, CommandExit.code] at h
      · simp [refused, CommandExit.code] at h

theorem readKind_worldLook {E : Env D} {w : World D} {id : D} {k : Nat} {cell : Cell}
    (h : readKind (worldLook E w) id k = .ok cell) : w.live E id = some cell ∧ cell.kind = k := by
  unfold readKind worldLook at h
  split at h
  · cases h
  · cases h
  · rename_i cl hl
    simp only [Except.ok.injEq] at hl
    split at h
    · cases h; exact ⟨hl, by assumption⟩
    · cases h

/-- A package read depends on the World only through the package's own cell. -/
theorem readPackage_live {E : Env D} {w w' : World D} {P : D} (h : w.live E P = w'.live E P) :
    Lang.readPackage (worldLook E w) P = Lang.readPackage (worldLook E w') P := by
  simp only [Lang.readPackage, readKind, worldLook, h]

theorem invokedPackage_at {X : Ctx D} {w : World D} {obj P : D} {pc : Cell} {pk : D}
    (hp : PackageAt X w obj P pc) (h : invokedPackage X w obj = .ok pk) : pk = P := by
  obtain ⟨⟨cell, hl, -, hpk⟩, -, -⟩ := hp
  unfold invokedPackage at h
  rw [hl] at h
  simp only [hpk, bind, Except.bind, requireMethods] at h
  cases h; rfl

/-- **The `core` line of a description is the package cell's bytes**: the one line of `describeText`
in `core` form is the hex of slot 0 of the live cell at the object's package. -/
theorem describeText_core {X : Ctx D} {w : World D} {obj : D} {cell : Cell} {ls : List String}
    (h : describeText X w obj cell = .ok ls) {l : String} (hl : l ∈ ls) {hx : List Char}
    (hm : Resident.coreWords l.toList = some hx) :
    ∃ P pc b, packageOf X obj cell = .ok (some P) ∧ w.live X.env P = some pc ∧ pc.slots.get 0 = some b ∧
      hx = (Lang.Print.hex b).toList := by
  unfold describeText at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i v hv
  cases h
  rcases List.mem_cons.mp hl with rfl | hl
  · simp [toString, Resident.coreWords] at hm
  rcases List.mem_append.mp hl with hl | hl
  · cases ho : cell.slots.get slotOwner with
    | none => simp [ho] at hl
    | some ow =>
      simp [ho] at hl
      subst hl
      simp [toString, Resident.coreWords] at hm
  unfold describeLines at hv
  simp only [bind, Except.bind, pure, Except.pure] at hv
  cases hp : packageOf X obj cell with
  | error e => simp [hp, Except.mapError] at hv
  | ok pkg =>
  cases hlw : lawsOf X obj cell with
  | error e => simp [hp, hlw, Except.mapError] at hv
  | ok laws =>
  simp only [hp, hlw, Except.mapError] at hv
  cases pkg with
  | none =>
    simp only at hv
    split at hv
    · cases hv
    · rename_i r hr
      cases hv
      rcases List.mem_append.mp hl with hl | hl
      · simp only [List.mem_singleton] at hl
        subst hl
        simp [Resident.coreWords] at hm
      · obtain ⟨x, -, hx⟩ := Lifetime.mapM_ok_mem hr l hl
        repeat' split at hx
        all_goals first | (cases hx; done) | skip
        cases hx
        simp [toString, Resident.coreWords] at hm
  | some P =>
    simp only at hv
    split at hv
    · cases hv
    · rename_i pk hpk
      split at hv
      · rename_i pls hpls
        split at hv
        · cases hv
        · rename_i r hr
          cases hv
          have hrp : Lang.readPackage (worldLook X.env w) P = .ok pk := by
            split at hpk
            · cases hpk
            · cases hpk; assumption
          obtain ⟨pc, b, hrk, -, hb, -⟩ := Lang.readPackage_ok.mp hrp
          have hpl := (readKind_worldLook hrk).1
          rcases List.mem_cons.mp hl with rfl | hl
          · simp [toString, Resident.coreWords] at hm
          rcases List.mem_cons.mp hl with rfl | hl
          · refine ⟨P, pc, b, rfl, hpl, hb, ?_⟩
            simp only [hpl, hb, Option.bind_some, Option.getD_some] at hm
            simp [toString, Resident.coreWords] at hm
            exact hm.symm
          rcases List.mem_append.mp hl with hl | hl
          · rw [packageLines_core hpls hl] at hm; cases hm
          · obtain ⟨x, -, hx⟩ := Lifetime.mapM_ok_mem hr l hl
            repeat' split at hx
            all_goals first | (cases hx; done) | skip
            cases hx
            simp [toString, Resident.coreWords] at hm
      · cases hv

omit [Ord D] [DecidableEq D] in
/-- What a describe reply the resident accepted is (HOSTING-49): UTF-8 text whose `object` line names
the configured bell, and which `Shape.read` reads as the shape. -/
theorem describeOut_ok {c : Resident.Conf} {r : Resident.Reply} {sh : Resident.Shape}
    (h : Resident.describeOut c r = .ok sh) :
    ∃ out, String.fromUTF8? r.stdout = some out ∧
      Resident.objectNamed c.bell (Resident.splitLines out.toList) = true ∧ Resident.Shape.read out = .ok sh := by
  unfold Resident.describeOut at h
  split at h
  · cases h
  · rename_i out hout
    unfold Resident.Shape.ofDescription at h
    split at h
    · rename_i hn
      refine ⟨out, hout, hn, ?_⟩
      cases hr : Resident.Shape.read out with
      | error e => rw [hr] at h; cases h
      | ok sh' => rw [hr] at h; simp only [Except.mapError, Except.ok.injEq] at h; rw [h]
    · cases h

omit [Ord D] [DecidableEq D] in
/-- **The shape the resident holds is the configured bell's** (HOSTING-49, READ-HOSTING Q4): a describe
reply that reads as a shape has an `object` line whose hex is the config's bell id. With
`Lifetime.shape_provenance`, every invoke is sent at the shape of a description that named
`w.conf.bell`, checked where the description entered, not only under `StdioLeg`. -/
theorem describedShape_names_bell {c : Resident.Conf} {y : Except String Resident.Reply} {sh : Resident.Shape}
    (h : Resident.describedShape c y = some sh) :
    ∃ rd out hx, y = .ok rd ∧ String.fromUTF8? rd.stdout = some out ∧
      (Resident.splitLines out.toList).findSome? Resident.objectWords = some hx ∧
      Text.ofHex (String.ofList hx) = some c.bell := by
  unfold Resident.describedShape at h
  split at h
  · rename_i rd
    split at h
    · cases hr : Resident.describeOut c rd with
      | error _ => rw [hr] at h; cases h
      | ok sh' =>
        obtain ⟨out, hout, hn, -⟩ := describeOut_ok hr
        unfold Resident.objectNamed at hn
        split at hn
        · rename_i hx hf
          exact ⟨rd, out, hx, rfl, hout, hf, by simpa using hn⟩
        · cases hn
    · cases h
  · cases h

omit [Ord D] [DecidableEq D] in
/-- What `bellCore` accepting says: the first `core` line's hex is a package's bytes, and that
package is the Bell. -/
theorem bellCore_ok {ls : List (List Char)} {p : Lang.Package} (h : Resident.bellCore ls = .ok p) :
    ∃ hx b, ls.findSome? Resident.coreWords = some hx ∧ Text.ofHex (String.ofList hx) = some b ∧
      Lang.Wire.decodePackage b = .ok p ∧ Lang.Bell.shapeOk p = true := by
  unfold Resident.bellCore at h
  cases hf : ls.findSome? Resident.coreWords with
  | none => simp [hf] at h
  | some hx =>
    cases hb : Text.ofHex (String.ofList hx) with
    | none => simp [hf, hb] at h
    | some b =>
      cases hd : Lang.Wire.decodePackage b with
      | error e => simp [hf, hb, hd] at h
      | ok q =>
        by_cases hs : Lang.Bell.shapeOk q = true
        · simp only [hf, hb, hd, hs, if_true, pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨hx, b, rfl, hb, hd, hs⟩
        · simp [hf, hb, hd, hs] at h

/-- **Trigger (iii): a description that reads as a shape says the method's declared argument type.**
If follow described `obj` on `w` (`ok`) and the resident read that text as the shape `sh`, then on
`w` the object is live, an object, with package `P` in a live ROM cell (`PackageAt`), and the
package's method at `sh.answer` is labelled `answer` with argument type exactly `answerArgTy`: the
line the resident read is that method's line (no other line of a description begins `method`, and
none holds a break, `describe`'s `noBreak`), its words are the index, the label and the type text
(the label one atom, `methodLine`'s `labelAtom`), and the type text reads back as the declared type
(`Lang.Print.readTy_ty`, the type well formed, `methodLine`'s `Ty.wf`). And the package IS the Bell
(`Lang.Bell.shapeOk`, HOSTING-45): the one `core` line is the package cell's bytes
(`describeText_core`), which the resident decoded and checked (`bellCore_ok`), and which
`readPackage` decodes to `pk`. -/
theorem describe_shape {X : Ctx D} {w : World D} {obj : D} {o e : ByteArray} {sh : Resident.Shape}
    (h : describe X w obj = .done CommandExit.ok.code.toUInt8 o e)
    (hs : Resident.Shape.read ((String.fromUTF8? o).getD "") = .ok sh) :
    ∃ P pc pk sg, PackageAt X w obj P pc ∧ Lang.readPackage (worldLook X.env w) P = .ok pk ∧
      Lang.resolveMethod (D := D) pk sh.answer = .ok ("answer", sg) ∧ sg.arg = Resident.answerArgTy ∧
      Lang.Bell.shapeOk pk = true := by
  obtain ⟨cell, ls, hl, hk, ht, hnb, rfl⟩ := describe_ok_text h
  rw [fromUTF8_toUTF8'] at hs
  simp only [Option.getD_some] at hs
  obtain ⟨⟨q, hq⟩, i, ty, haw, hi, hty⟩ := shape_read_ok hs
  rw [splitLines_join ls hnb] at haw hq
  -- the core line: the package cell's bytes, which decode to the Bell
  obtain ⟨hx, bq, hfx, hbq, hdq, hsq⟩ := bellCore_ok hq
  obtain ⟨lc, hlcm, hlc⟩ := List.exists_of_findSome?_eq_some hfx
  have hcore : ∀ (P : D) (pk : Lang.Package), packageOf X obj cell = .ok (some P) →
      Lang.readPackage (worldLook X.env w) P = .ok pk → Lang.Bell.shapeOk pk = true := by
    intro P pk hpP hrP
    rcases List.mem_append.mp hlcm with hlcm | hlcm
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hlcm
      obtain ⟨P', pc', b', hpP', hpl', hb', rfl⟩ := describeText_core ht hl' hlc
      rw [hpP] at hpP'
      cases hpP'
      rw [String.ofList_toList, ofHex_hex] at hbq
      cases hbq
      obtain ⟨pc'', b'', hrk, -, hb'', hd''⟩ := Lang.readPackage_ok.mp hrP
      rw [(readKind_worldLook hrk).1] at hpl'
      cases hpl'
      rw [hb'] at hb''
      cases hb''
      rw [hdq] at hd''
      cases hd''
      exact hsq
    · simp only [List.mem_singleton] at hlcm
      subst hlcm
      simp [Resident.coreWords] at hlc
  obtain ⟨l, hlm, hmw⟩ := answerWords_some haw
  rcases List.mem_append.mp hlm with hlm | hlm
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hlm
    obtain ⟨P, pk, j, ℓ, sg, a, hpk, hrp, hres, hat, hwf, hpty, rfl⟩ := describeText_method ht hl' hmw
    rw [methodWords_line j a hat] at hmw
    simp only [Option.some.injEq, Prod.mk.injEq] at hmw
    obtain ⟨rfl, rfl, rfl⟩ := hmw
    have hj : (toString j).toNat? = some j := Nat.toNat?_repr j
    rw [hj] at hi
    obtain rfl := Option.some.inj hi
    rw [Lang.Print.readTy_ty hwf hpty] at hty
    obtain ⟨pc, b, hrk, hrom, -, -⟩ := Lang.readPackage_ok.mp hrp
    exact ⟨P, pc, pk, sg, ⟨⟨cell, hl, hk, hpk⟩, (readKind_worldLook hrk).1, hrom⟩, hrp, hres,
      Except.ok.inj hty, hcore P pk hpk hrp⟩
  · simp only [List.mem_singleton] at hlm
    subst hlm
    simp [Resident.methodWords] at hmw

/-! ## The strong form -/

/-- **The delivered answer is the resident's datum, committed on the member's own World** (the
strong form of `delivered_answer_committed`, R-0065; premise `StdioLeg`, the `stdio-*` and `follow-loop` rows (HOSTING-50),
nothing more; codec premise `hX`, discharged at the deployed codec by
`Codec.Proofs.Deployed.eq_callBytes_of_decodeCall`). In one resident process's lifetime (`run` starts
it with no shape and the volume's seed, `Lifetime.seed_ok`), an invoke of `answer` for `(r, t)` whose
reply came back `ok`: follow's World at its `ok` journals a call of the member's, invoking the
object the config's `bell` names at the method the description read, through the config's grant,
whose argument bytes ARE `answerDatum r t` at `answerArgTy`: the ring's key, its text, and the
answer, exactly.

The join, each step a theorem: the shape the invoke was sent at was read from a describe earlier
in the same process (`Lifetime.shape_provenance`, trigger (i)); that describe was follow's own
description of the bell on a World `wd` (`run_describe_ok`), which says the bell's package `P`, in
a ROM cell, has at `sh.answer` a method `answer` of type `answerArgTy` (`describe_shape`, trigger
(iii)); follow's World moved from `wd` to the World it planned the invoke on only by its own frames
(`StdioLeg`'s one follower), each of which keeps the bell's package and the package's cell
(`reach_packageAt`, `Protocol.Command.step_packageAt`, KERNEL-64: trigger (ii)); so the invoke read
the text at `answerArgTy` (`answer_args_at_answerArgTy`), and the ring and answer are within Lang's
bounds (`Lifetime.lifetime_bounds`). The last conjunct names the method the call runs and where its
commit is to be found: the call's canonical bytes read back as itself (step 3 checks it before it
submits); on the World `wb` the invoke's run started at, from which follow's own frames reach the
settling World `wf`, the bell holds package `P` in a ROM cell (`PackageAt`), `P` reads as `pk`, and
`pk`'s method at `sh.answer` is labelled `answer`, and `pk` IS the Bell (`Lang.Bell.shapeOk`: the
resident's own check of the description's `core` line, HOSTING-45), which is what
`BellRow.answered_row_is_kept_answer` runs and `BellRow.answered_row_committed` takes to the commit
(HOSTING-44; over the frames' results `S` of `Reach`, an entry absent at `wb`, HOSTING-47). -/
theorem delivered_answer_committed_strong [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D}
    {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D} {w : Resident.Where} {m : Resident.Mem}
    {ess : List (List Resident.Ev)}
    (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (h : ResidentRun.Ticks w m ess) (hm : m.shape = none) (hk : Lifetime.KeptOk m.kept)
    (hs : StdioLeg X dc B me w.conf (Resident.core ess.flatten))
    {sh : Resident.Shape} {r : Resident.Ring} {t : ByteArray} {rr : Resident.Reply}
    (hi : Resident.Ev.cmd (.invoke sh r t) (.ok rr) ∈ Resident.core ess.flatten)
    (hok : rr.exit = CommandExit.ok.code) :
    ∃ (o g : D) (wf : World D) (u : Unsigned D) (sig : ByteArray) (hh : Nat) (td : D) (args : ByteArray),
      X.digestOf w.conf.bell = some o ∧ X.digestOf w.conf.grant = some g ∧
      u.member = me.member ∧ u.body = .invoke o sh.answer args invokeBudget (some g) ∧
      Lang.Wire.encodeData Resident.answerArgTy (Resident.answerDatum r t) = some args ∧
      wf.journalAt X.env (txIdOf X ⟨u, sig⟩) = some (hh, td) ∧
      X.decodeCall (X.callBytes ⟨u, sig⟩) = some ⟨u, sig⟩ ∧
      ∃ (wb : World D) (P : D) (pc : Cell) (pk : Lang.Package) (sg : Lang.Sig), Reach X dc B me wb wf ∧
        PackageAt X wb o P pc ∧
        Lang.readPackage (worldLook X.env wb) P = .ok pk ∧ Lang.resolveMethod (D := D) pk sh.answer = .ok ("answer", sg) ∧
        Lang.Bell.shapeOk pk = true := by
  -- (i): the shape came from an earlier describe in this process
  rcases Lifetime.shape_provenance h hi with hsh | ⟨y, pre, mid, post, hc, hy⟩
  · rw [hm] at hsh; cases hsh
  obtain ⟨rd, rfl, hdok, hshape⟩ : ∃ rd, y = .ok rd ∧ rd.exit = CommandExit.ok.code ∧
      Resident.Shape.read ((String.fromUTF8? rd.stdout).getD "") = .ok sh := by
    unfold Resident.describedShape at hy
    split at hy
    · rename_i rd
      split at hy
      · rename_i hx
        refine ⟨rd, rfl, hx, ?_⟩
        cases hr : Resident.describeOut w.conf rd with
        | error _ => rw [hr] at hy; cases hy
        | ok sh' =>
          rw [hr] at hy; cases hy
          obtain ⟨out, hout, -, hs⟩ := describeOut_ok hr
          rw [hout]; exact hs
      · cases hy
    · cases hy
  -- the one follower: the describe's run, then the invoke's, from a World follow reached
  obtain ⟨w₀, hl⟩ := hs
  rw [hc, List.append_assoc, List.cons_append] at hl
  obtain ⟨w₁, -, hl₁⟩ := legFrom_suffix pre hl
  obtain ⟨fd₀, fde, -, hrd, hl₂⟩ := legFrom_ok hl₁ hdok
  obtain ⟨w₂, hr₂, hl₃⟩ := legFrom_suffix mid hl₂
  obtain ⟨fi₀, fie, hr₃, hri, -⟩ := legFrom_ok hl₃ hok
  -- (iii): the describe's run is follow's description of the bell on `fde`'s World
  have hdp : ∀ cmd, Command.parse X.digestOf (Resident.Cmd.describe.argv w.conf) = .ok cmd →
      ∃ obj, cmd = .describe obj := by
    intro cmd hp
    obtain ⟨o, -, rfl⟩ := describeArgv_parse hp
    exact ⟨o, rfl⟩
  obtain ⟨od, hpd, hdesc⟩ := run_describe_ok (w₀ := fd₀.world) hdp hrd start_contOf (.refl _)
    (fun _ _ => start_ne_ok) (by simp [hdok])
  obtain ⟨od', hbd, hod⟩ := describeArgv_parse hpd
  cases hod
  obtain ⟨P, pc, pk, sg, hpat, hrp, hres, harg, hbell⟩ := describe_shape hdesc hshape
  -- the invoke's run: a planned call, committed
  obtain ⟨txt, htxt⟩ := Option.isSome_iff_exists.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some r t)
  have hv : (Resident.Cmd.invoke sh r t).argv w.conf = Resident.invokeArgv w.conf sh txt := by
    unfold Resident.Cmd.argv
    dsimp only
    rw [htxt]
  rw [hv] at hri
  have hinv : ∀ cmd, Command.parse X.digestOf (Resident.invokeArgv w.conf sh txt) = .ok cmd →
      ∃ obj m a rg via, cmd = .invoke obj m a rg via := by
    intro cmd hp
    obtain ⟨o, g, -, -, rfl⟩ := invokeArgv_parse hp
    exact ⟨_, _, _, _, _, rfl⟩
  obtain ⟨gf, hgf, acc, ⟨wp, hrp', cmd, s, rs, b, u, sig, hp, hb, hrs, hpl, hacc, hrt⟩, cb, c, hh, td, hcb, hdc, hset⟩ :=
    run_invoke_ok (w₀ := fi₀.world) hinv hri (.refl _) start_contOf (fun _ _ => start_ne_ok) (by simp [hok])
  rw [hacc] at hcb
  cases hcb
  obtain ⟨o, g, ho, hg, rfl⟩ := invokeArgv_parse hp
  rw [hbd] at ho
  cases ho
  obtain ⟨pk', args, hpk', hargs, rfl⟩ := body_invoke hb
  -- (ii): follow's own frames kept the bell's package and its ROM cell from `fde` to `wp`
  have hpat' := reach_packageAt (hr₂.trans (hr₃.trans hrp')) hpat
  obtain rfl := invokedPackage_at hpat' hpk'
  -- the invoke read the text at `answerArgTy`
  obtain ⟨hrk, hbt⟩ := Lifetime.lifetime_bounds h hk hi
  obtain ⟨hn, hx, hgr, hai⟩ := hrk
  obtain ⟨pk'', ℓ, sg', hrp'', hres'', henc⟩ :=
    answer_args_at_answerArgTy hn hx hgr hai hbt htxt hargs
  rw [readPackage_live (hpat'.2.1.trans hpat.2.1.symm), hrp] at hrp''
  cases hrp''
  rw [hres] at hres''
  cases hres''
  obtain ⟨hmem, -, hbody, -⟩ := plan_admits hpl
  have htx : txIdOf X c = txIdOf X ⟨u, sig⟩ := by unfold txIdOf; rw [hX _ _ hdc]
  have hj := Protocol.Settle.settle_committed hset
  rw [htx] at hj
  have hpatB := reach_packageAt (hr₂.trans hr₃) hpat
  exact ⟨od, g, gf.world, u, sig, hh, td, args, hbd, hg, hmem, hbody, henc harg, hj, hrt, fi₀.world, _, pc, pk,
    sg, hgf, hpatB, (readPackage_live (hpatB.2.1.trans hpat.2.1.symm)).trans hrp, hres, hbell⟩

end Nanodregg.Hosting.Proofs.Socket
