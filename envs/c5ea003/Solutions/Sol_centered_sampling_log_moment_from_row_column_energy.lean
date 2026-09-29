-- Prove2me | solution 1 for centered_sampling_log_moment_from_row_column_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T18:33:58.159144+00:00
-- url     : https://prove2.me/submissions/55fba6d6-d58b-4308-ba84-30145f8d7a88

import Theorems.Thm_centered_sampling_symmetrization_moment_bound_of_sample_ratio
import Theorems.Thm_rademacher_sampled_matrix_moment_from_row_column_energy
import Theorems.Thm_centered_sampling_log_moment_scale_absorption

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF pp. 24--25, Section 6.1.  The reduction
uses equation (6.5), the Jensen/Rademacher symmetrization paragraph on PDF
p. 24, Lemma 6.1 on PDF p. 25, and the displayed row/column-energy moment
estimate (6.6).  In Lean this node combines the sample-ratio-safe
symmetrization bound, the Rademacher/Khintchine row-column energy estimate, and
the already-proved scale absorption into the final log-moment estimate. -/
theorem solution
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        (∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (Cmoment * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  intro hCenergy
  rcases centered_sampling_symmetrization_moment_bound_of_sample_ratio with
    ⟨Csym, hCsym, hSymm⟩
  rcases rademacher_sampled_matrix_moment_from_row_column_energy Cenergy
      hCenergy with
    ⟨Crad, hCrad, hRad⟩
  rcases centered_sampling_log_moment_scale_absorption Csym Crad
      hCsym hCrad with
    ⟨Cmoment, hCmoment, hScale⟩
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hEnergy
  rcases hEnergy with
    ⟨q, hqOne, hqLogLower, hqLogUpper, hqSamplingUpper, hEnergyBound⟩
  refine ⟨q, hqOne, hqLogLower, ?_⟩
  exact hScale β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne
    hqLogLower hqLogUpper
    (hSymm n₁ n₂ m q X hn₁ hn₂ hm hqOne)
    (hRad β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne
      hqLogLower hqLogUpper hqSamplingUpper hEnergyBound)
