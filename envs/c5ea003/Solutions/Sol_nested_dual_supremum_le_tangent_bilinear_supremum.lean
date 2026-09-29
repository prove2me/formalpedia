-- Prove2me | solution 1 for nested_dual_supremum_le_tangent_bilinear_supremum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T08:20:55.206287+00:00
-- url     : https://prove2.me/submissions/2437cbad-539b-4b92-8691-1673428e63fc

import Theorems.Thm_tangent_bilinear_deviation_candidates_bddAbove

open MatrixCompletion
open scoped Classical BigOperators

/-- Flatten the nested supremum by bounding each inner supremum by the single
supremum over admissible pairs.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2).  This is the formal `sSup` bookkeeping for the display rewriting `Z` as
a supremum over two test matrices. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingNestedDualDeviation Omega S p ≤
      tangentSamplingTangentBilinearDeviation Omega S p := by
  unfold tangentSamplingNestedDualDeviation tangentSamplingTangentBilinearDeviation
  refine csSup_le ?outer_nonempty ?outer_le
  · refine ⟨sSup {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
      frobeniusNorm X1 ≤ 1 ∧
        w = p⁻¹ * matrixInner X1
          (tangentProjection S (samplingProjection Omega 0) -
            p • (0 : Matrix (Fin n₁) (Fin n₂) ℝ))}, ?_⟩
    refine ⟨0, ?_, ?_, rfl⟩
    · ext i j
      simp [tangentProjection, leftSingularProjection, rightSingularProjection,
        twoSidedSingularProjection]
    · unfold frobeniusNorm frobeniusNormSq
      simp
  · intro b hb
    rcases hb with ⟨X2, hT, hX2, rfl⟩
    refine csSup_le ?inner_nonempty ?inner_le
    · refine ⟨0, ?_⟩
      refine ⟨0, ?_, ?_⟩
      · unfold frobeniusNorm frobeniusNormSq
        simp
      · simp [matrixInner]
    · intro w hw
      rcases hw with ⟨X1, hX1, rfl⟩
      refine le_csSup (tangent_bilinear_deviation_candidates_bddAbove Omega S p) ?_
      exact ⟨X1, X2, hX1, hT, hX2, rfl⟩
