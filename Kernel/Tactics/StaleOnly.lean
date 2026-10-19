/-
# Kernel.Tactics.StaleOnly — the `stale_only` tactic (PROTOCOL-20, KERNEL-23 agreed)

A proof-only tactic, specific to the stale analysis: it closes a `StaleOnly` goal of
`Kernel.Proofs.StaleOnly` built of `req`, `bind`, `forEx`, `mapEx`, `noDup`, matches and refusals
other than `stale`. Only `Kernel.Proofs.StaleOnly` imports it; no deployed module does. It is a def
module because a proof module exports no macro (closure C3). The lemmas it applies are
`StaleOnly.ok`, `.pure'`, `.noDup`, `.req`, `.error`, `.forEx`, `.mapEx` and `.bind`, named by plain
identifiers (`mkIdent`, no macro scopes), so they resolve where the tactic runs, after
`Kernel.Proofs.StaleOnly` has stated them.
-/

namespace Nanodregg.Kernel

/-- Close a `StaleOnly` goal by its closure lemmas; `apply` of the monadic ones is reducible-only,
since `StaleOnly.bind` unifies with any `Except` term (`x := pure ()`) otherwise and loops. -/
macro "stale_only" : tactic => do
  let ok := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.ok
  let pure' := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.pure'
  let noDup := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.noDup
  let req := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.req
  let error := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.error
  let forEx := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.forEx
  let mapEx := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.mapEx
  let bind := Lean.mkIdent `Nanodregg.Kernel.StaleOnly.bind
  `(tactic| repeat' (first
    | exact $ok:ident _
    | exact $pure':ident _
    | (apply $noDup:ident; intro _ _ h; cases h; done)
    | (with_reducible apply $req:ident; intro _ h; cases h; done)
    | (with_reducible apply $error:ident; intro _ h; cases h; done)
    | (with_reducible apply $forEx:ident; intros)
    | (with_reducible apply $mapEx:ident; intros)
    | (with_reducible apply $bind:ident <;> intros)
    | split))

end Nanodregg.Kernel
