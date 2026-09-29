-- Prove2me | solution 1 for bernoulli_sampled_row_column_energy_controlled_log_moment_bound_of_two_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T18:48:55.923973+00:00
-- url     : https://prove2.me/submissions/a3136117-f0bb-4f1a-b0b4-1b23878afd29

import Theorems.Thm_fixed_matrix_sampling_log_moment_exponent_window_exists_of_two_sample_lower
import Theorems.Thm_bernoulli_sampled_row_energy_moment_bound
import Theorems.Thm_bernoulli_sampled_column_energy_moment_bound
import Theorems.Thm_sampled_row_column_energy_max_moment_from_row_and_column_bounds_of_sample_ratio

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF p. 25, Lemma 6.2, estimate (6.6), and the
following paragraph saying the same estimate applies to the column term and
hence to the maximum of the two row/column energy quantities.  This corrected
reduction also uses the repaired integer moment-window lemma with the explicit
conditions needed to choose `q = ceil (β log n)`. -/
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
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  rcases bernoulli_sampled_row_energy_moment_bound with
    ⟨Crow, hCrow, hRow⟩
  rcases bernoulli_sampled_column_energy_moment_bound with
    ⟨Ccol, hCcol, hColumn⟩
  rcases sampled_row_column_energy_max_moment_from_row_and_column_bounds_of_sample_ratio
      Crow Ccol with
    ⟨C, hC, hMax⟩
  refine ⟨C, hC, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hLogWindow hSample
  rcases fixed_matrix_sampling_log_moment_exponent_window_exists_of_two_sample_lower
      β hβ n₁ n₂ m hn₁ hn₂ hm hLogWindow hSample with
    ⟨q, hqOne, hqLogLower, hqLogUpper, hqSamplingUpper⟩
  have hRowBound :=
    hRow β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLogLower
      hqSamplingUpper
  have hColumnBound :=
    hColumn β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLogLower
      hqSamplingUpper
  exact ⟨q, hqOne, hqLogLower, hqLogUpper, hqSamplingUpper,
    hMax m q X hn₁ hn₂ hm hqOne hCrow hCcol hRowBound hColumnBound⟩
