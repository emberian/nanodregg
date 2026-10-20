/-
P11a/P9 integration: actual recorded contextual nogoods produce losing completion
games. de Kleer (1986), printed pp144–145; Köhler et al. (2013), PDF pp3–4.
P9 owns the imported policy. P11a adds no premise to a landed theorem.
-/
import Lang.Proofs.Contextual.Nogoods
import Lang.Proofs.Contextual.NogoodGames

namespace Nanodregg.Lang.Contextual.P5.NogoodGames

/-- de Kleer, printed p145; Köhler et al., PDF p4: P9's actual refuted candidate
is a losing singleton completion game, with its recorded inconsistent assumption set.
This is a question about this candidate, not all possible fillings of a hole. -/
theorem recorded_candidate_is_lost {D : CalculusData} {E : Type}
    {cl : P9.RecordedClosure D E} {I : Iface D E} {w : World E}
    {c : Candidate D} {ng : List Token}
    (h : P9.classifyRecorded cl I w c = .refuted ng) :
    ng ∈ cl.nogoods ∧ (∀ t ∈ ng, t ∈ effSupports I c) ∧
      Games.Solved
        (moves (⟨[()], fun _ => decide ((P9.judgeRecorded cl I w c).status = .verified)⟩ :
          Problem Unit)) false .question := by
  obtain ⟨hm, hs, hn⟩ := P9.recorded_refuted h
  refine ⟨hm, hs, excluded_loses ?_⟩
  intro a _
  exact decide_eq_false (hn w)

/-- de Kleer, printed p145; Köhler et al., PDF p4: P9's replayed nogood constructs
a real refutation through the new checker. Record membership, support inclusion and
current rejection are rechecked, rather than a LogicalStatus constructor being trusted. -/
theorem recorded_candidate_constructs_refutation {D : CalculusData} {E : Type}
    {cl : P9.RecordedClosure D E} {I : Iface D E} {w : World E}
    {c : Candidate D} {ng : List Token}
    (h : P9.classifyRecorded cl I w c = .refuted ng) :
    judge (⟨[()], fun _ => decide ((P9.judgeRecorded cl I w c).status = .verified)⟩ :
      Problem Unit) [] (fun _ => effSupports I c) cl.nogoods (some [((), ng)]) =
        .refuted [((), ng)] := by
  obtain ⟨hm, hs, hn⟩ := P9.recorded_refuted h
  have hsub : (ng.all fun t => decide (t ∈ effSupports I c)) = true := by
    simpa [List.all_eq_true] using hs
  simp [judge, P5.judge, checkCertificate, hm, hsub, hn w]

end Nanodregg.Lang.Contextual.P5.NogoodGames
