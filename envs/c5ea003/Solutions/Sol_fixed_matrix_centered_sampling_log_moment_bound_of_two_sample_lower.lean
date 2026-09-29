-- Prove2me | solution 1 for fixed_matrix_centered_sampling_log_moment_bound_of_two_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T08:41:27.99394+00:00
-- url     : https://prove2.me/submissions/d5723205-f7de-4ec9-afe6-59375f8f5b5d

import Theorems.Thm_bernoulli_sampled_row_column_energy_controlled_log_moment_bound_of_two_sample_lower
import Theorems.Thm_centered_sampling_log_moment_from_row_column_energy

open MatrixCompletion

/-- Repair the fixed-matrix log-moment reduction by routing it through the
corrected controlled row/column energy estimate, whose exponent window exposes
`q ≤ 2 β log n` and `q ≤ p n`. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (1 : ℝ) ≤ β * Real.log (↑(max n₁ n₂)) →
        (m : ℝ) ≥ 2 * β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (C * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  rcases
      bernoulli_sampled_row_column_energy_controlled_log_moment_bound_of_two_sample_lower with
    ⟨Cenergy, hCenergy, hEnergy⟩
  rcases centered_sampling_log_moment_from_row_column_energy Cenergy
      hCenergy with
    ⟨Cmoment, hCmoment, hKhintchine⟩
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hLogWindow hSampleTwo
  have hN_pos : 0 < (↑(max n₁ n₂) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hLogScale_nonneg :
      0 ≤ β * Real.log (↑(max n₁ n₂)) := by
    exact le_trans (by norm_num) hLogWindow
  have hSampleOne :
      (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
        Real.log (↑(max n₁ n₂)) := by
    nlinarith
  have hEnergyBound :=
    hEnergy β hβ n₁ n₂ m X hn₁ hn₂ hm hLogWindow hSampleTwo
  exact hKhintchine β hβ n₁ n₂ m X hn₁ hn₂ hm hSampleOne
    hEnergyBound
