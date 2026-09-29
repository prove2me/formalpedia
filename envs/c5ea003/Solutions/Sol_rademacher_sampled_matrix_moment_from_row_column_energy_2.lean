-- Prove2me | solution 2 for rademacher_sampled_matrix_moment_from_row_column_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T19:33:21.915832+00:00
-- url     : https://prove2.me/submissions/14fe6a91-e798-48b7-813b-336f2f2a3494

import Theorems.Thm_rademacher_sampled_matrix_conditional_khintchine_bound
import Theorems.Thm_bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
import Theorems.Thm_conditional_khintchine_scale_moment_from_row_column_energy_moment

open MatrixCompletion

/-- Source: Candes-Recht 2008, Section 6.1, PDF p. 24 through PDF p. 25,
from the symmetrization/noncommutative-Khintchine estimate before Lemma 6.2,
Lemma 6.2/equation (6.6), and the paragraph leading to Theorem 6.3/equation
(6.7).

Decompose the Section 6.1 Khintchine conversion into the conditional
noncommutative-Khintchine estimate and the Bernoulli moment calculation for the
sampled row/column energy scale.  The corrected integration child carries the
sample-ratio hypotheses already present in this parent, ensuring that the
Bernoulli weights are nonnegative when the pointwise conditional estimate is
summed over `Omega`. -/
theorem solution
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCenergy
  rcases rademacher_sampled_matrix_conditional_khintchine_bound with
    ⟨Ckh, hCkh, hConditionalKhintchine⟩
  rcases conditional_khintchine_scale_moment_from_row_column_energy_moment
      Cenergy Ckh hCenergy hCkh with
    ⟨Crad, hCrad, hScaleMoment⟩
  refine ⟨Crad, hCrad, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne hqLogLower
    hqLogUpper hqSamplingUpper hEnergy
  have hRadScale :=
    bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
      Ckh n₁ n₂ m q X hn₁ hn₂ hm
      (fun Omega =>
        hConditionalKhintchine β hβ n₁ n₂ m q Omega X hqOne
          hqLogLower)
  have hScaleFinal :=
    hScaleMoment β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne
      hqLogLower hqLogUpper hqSamplingUpper hEnergy
  exact le_trans hRadScale hScaleFinal
