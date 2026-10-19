-- Prove2me | solution 1 for ExtendedSmale9.sec_9_6_i_imp_ii
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:30:19.572107+00:00
-- url     : https://prove2.me/submissions/4f74d4f5-72ee-4d3c-bc68-0d6ac5e0942f

import Definitions.Def_ExtendedSmale9_GeneralAlgorithm
import Definitions.Def_ExtendedSmale9_Delta1
import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib

open scoped ENNReal

open ExtendedSmale9 in
theorem solution {Ω Idx M : Type*} [MetricSpace M]
    (Λ : Idx → Ω → ℂ) (Ξ : Ω → Set M) (fhat : Idx → ℕ+ → Ω → ℂ)
    (hfhat : IsDelta1Info Λ fhat) :
    strongBreakdownEps (delta1Eval fhat) Ξ ≤
      strongBreakdownEps (delta1InputEval Λ) (fun q => Ξ q.input) := by
  let emb : Ω → Delta1Input Λ := fun ι => ⟨(ι, fun j n => fhat j n ι), fun j n => hfhat j n ι⟩
  apply sSup_le_sSup
  intro ε hε Γt
  let Γ : GeneralAlgorithm (delta1Eval fhat) M :=
    { run := fun ι => Γt.run (emb ι)
      queried := fun ι => Γt.queried (emb ι)
      queried_nonempty := fun ι => Γt.queried_nonempty (emb ι)
      queried_finite := fun ι h => Γt.queried_finite (emb ι) h
      run_eq_of_agree := fun ι ι' h => Γt.run_eq_of_agree (emb ι) (emb ι') h
      queried_eq_of_agree := fun ι ι' h => Γt.queried_eq_of_agree (emb ι) (emb ι') h }
  obtain ⟨ι, hι⟩ := hε Γ
  exact ⟨emb ι, hι⟩
