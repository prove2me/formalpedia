-- Prove2me | solution 1 for talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_dense
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-25T02:37:54.033276+00:00
-- url     : https://prove2.me/submissions/27de3e3e-743e-4f7f-9bdc-5312eaff773e

import Definitions.Def_matrix_completion_talagrand
import Theorems.Thm_talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense
import Theorems.Thm_a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min

open MatrixCompletion

/-
REDUCTION of db094af7_dense
`talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_dense`
onto two children:
  (8a1508ad, PROVED) `a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min`
      — supplies the increment (B) + variance (σ²) bounds from A0 alone, at the
        achievable coefficient `2 μ₀ max r / m`, AND
  (e5bb2914_dense) `talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense`
      — the density-threaded core that consumes those Inc/Var bounds.

`around_expectation` drops the Inc/Var hypotheses (only A0/A1 + density), so the
reduction RE-DERIVES them via 8a1508ad (using `0 < m`) and passes them to
e5bb2914_dense.  The reduction body is sorry-free; only the imported children carry
sorry (e5bb2914_dense is the still-Open core, 8a1508ad is Proved).

Source: CR2009 §9.1 (the Inc/Var bounds = eq. (4.8) coordinate-Frobenius scale;
the deviation step = Thm 9.1 eq. (9.2)).
-/

theorem solution
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
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
                (tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
                  tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCexpect
  obtain ⟨Ctail, c, hCtail0, hc0, hCore⟩ :=
    talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense
      Cexpect hCexpect
  refine ⟨Ctail, c, hCtail0, hc0, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm0 hm hμ₀ hμ₁ hA0 hA1 hdens hEZ
  obtain ⟨hInc, hVar⟩ :=
    a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
      n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm0 hm hμ₀ hA0
  exact hCore β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hdens hInc hVar hEZ
