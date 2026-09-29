-- Prove2me | solution 1 for talagrand_tangent_sampling_absolute_deviation_raw_tail_pos_with_expectation_le_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-22T15:10:55.50916+00:00
-- url     : https://prove2.me/submissions/8db6a8d0-04c7-4a5b-8a62-2f5d4c92fe91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_talagrand_tangent_sampling_absolute_deviation_raw_tail_with_expectation_le_one

open MatrixCompletion

/-!
Source: Candes--Recht, "Exact Matrix Completion via Convex Optimization",
Appendix 9.1, PDF pp. 46--47, Theorem 9.1/equation (9.2), as used in
Theorem 4.2, PDF p. 19, equation (4.10).

This is a purely formal bridge.  The positive-sample version has the same
absolute-deviation conclusion as the existing Appendix 9.1 tangent Talagrand
node, plus extra hypotheses `0 < m`, `A0`, `A1`, and coherence lower bounds.
Those hypotheses are useful downstream when the Appendix 9.1 scale is
specialized, but they are not needed for this raw Talagrand implication.
-/

theorem solution :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r) (B : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))| ≤
                K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases talagrand_tangent_sampling_absolute_deviation_raw_tail_with_expectation_le_one with
    ⟨K, c, hK, hc, hTalagrand⟩
  refine ⟨K, c, hK, hc, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S B hn₁ hn₂ hr _hmpos hm _hμ₀ _hμ₁ _hA0 _hA1
    hEZ hIncrement hVariance
  exact hTalagrand β hβ n₁ n₂ r m M S B hn₁ hn₂ hr hm hEZ hIncrement hVariance
