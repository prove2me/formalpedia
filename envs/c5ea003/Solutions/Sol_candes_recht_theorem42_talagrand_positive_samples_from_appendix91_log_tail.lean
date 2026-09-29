-- Prove2me | solution 1 for candes_recht_theorem42_talagrand_positive_samples_from_appendix91_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T15:41:31.825295+00:00
-- url     : https://prove2.me/submissions/9a3777f7-4bd6-4312-b116-ca456cad3961

import Theorems.Thm_a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
import Theorems.Thm_talagrand_tangent_sampling_absolute_deviation_log_tail
import Theorems.Thm_talagrand_tangent_sampling_appendix91_polynomial_scale_from_log_tail
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes--Recht, PDF p. 19, Theorem 4.2 equation (4.10), and Appendix
9.1, PDF pp. 46--47.

This is the corrected positive-sample Talagrand route.  It keeps the exact
logarithmic Talagrand tail from Theorem 9.1, obtains the Candes--Recht
increment and variance inputs from the proved min-dimension A0 bridge, and
then invokes the scalar Appendix 9.1 conversion from the logarithmic tail to
the displayed polynomial Theorem 4.2 scale.
-/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases talagrand_tangent_sampling_absolute_deviation_log_tail with
    ⟨K, hK, hLogTail⟩
  rcases talagrand_tangent_sampling_appendix91_polynomial_scale_from_log_tail K hK with
    ⟨C, c, hC, hc, hScalar⟩
  refine ⟨C, c, hC, hc, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hmpos hm hμ₀ hA0 hmLower hEZ
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let B : ℝ := 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)
  rcases
      a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
        n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hmpos hm hμ₀ hA0 with
    ⟨hIncrement, hVariance⟩
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hBnonneg : 0 ≤ B := le_of_lt hBpos
  have hLog :
      ∀ t : ℝ, 0 ≤ t →
        bernoulliEventProb p
            (fun Omega =>
              |tangentSamplingDeviation Omega S p -
                  bernoulliExpectation p
                    (fun Omega' => tangentSamplingDeviation Omega' S p)| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (B +
                      B * bernoulliExpectation p
                        (fun Omega' => tangentSamplingDeviation Omega' S p)))) := by
    intro t ht
    simpa [p, B] using
      hLogTail n₁ n₂ r m M S B B t hn₁ hn₂ hr hm hBpos hBnonneg ht
        hIncrement hVariance
  simpa [p, B] using
    hScalar C' hC' β hβ n₁ n₂ r m M μ₀ S
      hn₁ hn₂ hr hmpos hm hμ₀ hmLower hEZ hIncrement hVariance hLog

