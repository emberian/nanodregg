/- Environment-relative certificate reading. The reader adapter remains an explicit boundary. -/
import Census.CertificateReader

namespace Census.CertificateReader

variable {Name Expr Body : Type} [DecidableEq Name] [DecidableEq Expr] [DecidableEq Body]

/-- A footprint is closed under the reader's actual references, not just names the producer
chose to mention. Exact bodies, theory identity and admitted assumptions are retained. -/
structure Faithful (r : Reader Name Expr Body) (c : Certificate Name Expr Body) : Prop where
  checker : c.checker = r.checker
  target : ∃ body, r.lookup c.target = some body ∧ r.isTheorem body = true ∧
    c.statement = r.typeOf body ∧ (⟨c.target, body⟩ : Entry Name Body) ∈ c.context
  bodies : ∀ e ∈ c.context, r.lookup e.name = some e.body
  statement : ∀ n ∈ r.references c.statement, n ∈ names c
  closed : ∀ e ∈ c.context, ∀ n ∈ reads r e.body, n ∈ names c
  assumptions : c.assumptions = assumptions r c.context

private theorem any_target {ctx : List (Entry Name Body)} {n : Name} {b : Body}
    (h : (ctx.any fun e => decide (e.name = n ∧ e.body = b)) = true) :
    (⟨n, b⟩ : Entry Name Body) ∈ ctx := by
  have h' := List.any_eq_true.mp h
  simp only [decide_eq_true_eq] at h'
  obtain ⟨e, he, hn, hb⟩ := h'
  cases e
  simp_all

/-- The actual accepting branch establishes a complete environment-relative reading. -/
theorem accept_faithful {r : Reader Name Expr Body} {c : Certificate Name Expr Body}
    (h : accept r c = .ok ()) : Faithful r c := by
  unfold accept at h
  split at h
  · cases h
  · rename_i hc
    cases ht : r.lookup c.target with
    | none => simp only [ht] at h; cases h
    | some body =>
      simp only [ht] at h
      split at h
      · cases h
      · rename_i hk
        split at h
        · cases h
        · rename_i hs
          split at h
          · cases h
          · rename_i hm
            split at h
            · cases h
            · rename_i hb
              split at h
              · cases h
              · rename_i hr
                split at h
                · cases h
                · rename_i ha
                  simp only [ne_eq, Decidable.not_not] at hc hk hs hm hb hr ha
                  have hr' := List.all_eq_true.mp hr
                  simp only [decide_eq_true_eq] at hr'
                  refine ⟨hc, ⟨body, ht, hk, hs, any_target hm⟩, ?_, ?_, ?_, ha⟩
                  · simpa only [List.all_eq_true, decide_eq_true_eq] using hb
                  · intro n hn
                    exact hr' n (List.mem_append_left _ hn)
                  · intro e he n hn
                    exact hr' n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hn⟩))

/-- Successful bounded extraction satisfies the same reading contract as imported certificates.
The substantive closure property below is shared by both producers and consumers. -/
theorem read_faithful {r : Reader Name Expr Body} {c : Certificate Name Expr Body}
    {fuel : Nat} {target : Name} (h : read r fuel target = .ok c) : Faithful r c := by
  cases ht : r.lookup target with
  | none => simp [read, ht] at h
  | some body =>
    cases hg : gather r fuel [target] [] with
    | error e => simp [read, ht, hg] at h
    | ok ctx =>
      cases ha : accept r (Certificate.mk target (r.typeOf body) ctx (assumptions r ctx) r.checker) with
      | error e => simp [read, ht, hg, ha] at h
      | ok u =>
        cases u
        have hc : Certificate.mk target (r.typeOf body) ctx (assumptions r ctx) r.checker = c := by
          simpa [read, ht, hg, ha] using h
        subst c
        exact accept_faithful ha

/-- Any number of dependency expansions, starting at the statement or its proof declaration.
This includes cycles; no acyclicity or maximum unfolding depth is assumed in the theorem. -/
inductive Reaches (r : Reader Name Expr Body) (c : Certificate Name Expr Body) : Name → Prop
  | target : Reaches r c c.target
  | statement {n : Name} : n ∈ r.references c.statement → Reaches r c n
  | step {n next : Name} {body : Body} : Reaches r c n →
      r.lookup n = some body → next ∈ reads r body → Reaches r c next

/-- All constants reachable through the checked reader have an exact destination definition in
this certificate, even when the missing name would only appear after multiple unfoldings. -/
theorem accepted_reachable_definition {r : Reader Name Expr Body}
    {c : Certificate Name Expr Body} (h : accept r c = .ok ()) {n : Name}
    (reach : Reaches r c n) :
    ∃ body, (⟨n, body⟩ : Entry Name Body) ∈ c.context ∧ r.lookup n = some body := by
  have hf := accept_faithful h
  have named : ∀ n ∈ names c, ∃ body,
      (⟨n, body⟩ : Entry Name Body) ∈ c.context ∧ r.lookup n = some body := by
    intro n hn
    obtain ⟨e, he, hn⟩ := List.mem_map.mp hn
    subst n
    exact ⟨e.body, he, hf.bodies e he⟩
  induction reach with
  | target =>
    obtain ⟨body, ht, _, _, hm⟩ := hf.target
    exact ⟨body, hm, ht⟩
  | statement hr => exact named _ (hf.statement _ hr)
  | step hr hl hd ih =>
    obtain ⟨body, hm, hb⟩ := ih
    have heq := Option.some.inj (hb.symm.trans hl)
    subst body
    exact named _ (hf.closed _ hm _ hd)

/-- Removing a transitive dependency prevents acceptance; the path is read in the destination
reader, so deleting it from the producer's declared context cannot delete this obligation. -/
theorem missing_reachable_refused {r : Reader Name Expr Body}
    {c : Certificate Name Expr Body} {n : Name} (hr : Reaches r c n)
    (hm : n ∉ names c) : accept r c ≠ .ok () := by
  intro h
  obtain ⟨body, he, _⟩ := accepted_reachable_definition h hr
  exact hm (List.mem_map.mpr ⟨⟨n, body⟩, he, rfl⟩)

/-- A changed environment definition is not accepted merely because the target has the same
name and statement. Every declared payload is checked against the destination. -/
theorem changed_definition_refused {r : Reader Name Expr Body}
    {c : Certificate Name Expr Body} {e : Entry Name Body} (he : e ∈ c.context)
    (changed : r.lookup e.name ≠ some e.body) : accept r c ≠ .ok () := by
  intro h
  exact changed ((accept_faithful h).bodies e he)

omit [DecidableEq Name] [DecidableEq Expr] [DecidableEq Body]

/-- Same statement, different theory context: different certificate identities. No quotient by
statement or producer name silently erases the logic under which a claim was obtained. -/
theorem contexts_distinguish {a b : Certificate Name Expr Body}
    (different : a.context ≠ b.context) : a ≠ b := by
  intro h
  exact different (congrArg Certificate.context h)

/-- Checker identity is also intrinsic to certificate identity. -/
theorem checkers_distinguish {a b : Certificate Name Expr Body}
    (different : a.checker ≠ b.checker) : a ≠ b := by
  intro h
  exact different (congrArg Certificate.checker h)

end Census.CertificateReader
