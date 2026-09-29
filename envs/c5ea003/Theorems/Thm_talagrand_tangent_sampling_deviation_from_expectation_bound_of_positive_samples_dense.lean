-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_from_expectation_bound_of_positive_samples_dense
-- name    : talagrand_tangent_sampling_deviation_from_expectation_bound_of_positive_samples_dense
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-25T02:36:58.448391+00:00
-- url     : https://prove2.me/theorems/da5bf218-bbef-4edc-b876-eab4ef449d52
-- title:
--   Single-scale tangent deviation bound, density-threaded (positive samples)
-- statement:
--   **d55ec3ca_dense — density-threaded single-scale deviation bound (positive samples).** Density-correct version of `talagrand_tangent_sampling_deviation_from_expectation_bound_of_positive_samples` (d55ec3ca): single closed-form scale output $C\sqrt{\mu_0 n r\beta\log n/m}$. Reduces onto db094af7_dense (sum-scale bound) + the Proved helpers `sum_tangent_sampling_deviation_scales_le_single_scale` (6b8003d2, combine two scales), `bernoulli_tangent_sampling_deviation_bound_probability_mono` (27aef870, lift the probability bound), and `sample_ratio_between_zero_and_one` (c0188309, $p\in[0,1]$).
-- source:
--   Candes–Recht 2009 (arXiv:0805.4471) Theorem 4.1/4.2.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_from_expectation_bound_of_positive_samples_dense
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
