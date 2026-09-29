-- Prove2me | solution 2 for bernoulli_sampled_column_count_max_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-21T21:56:00.411593+00:00
-- url     : https://prove2.me/submissions/7088b864-3794-422e-a321-eefbd86646bf

import Definitions.Def_matrix_completion_sampled_counts
import Theorems.Thm_bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
import Theorems.Thm_bernoulli_sampled_column_count_max_large_deviation_bound
import Theorems.Thm_sampled_column_count_max_nonnegative
open MatrixCompletion

theorem solution :
    ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              sampledColumnCountMax Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  obtain ⟨Cdev, hCdev, hLD⟩ := bernoulli_sampled_column_count_max_large_deviation_bound
  obtain ⟨Cmoment, hCm, hmom⟩ :=
    bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound Cdev hCdev
  refine ⟨Cmoment, hCm, ?_⟩
  intro β hβ n₁ n₂ m q hn1 hn2 hm hq hqlog hqmu
  exact hmom β hβ n₁ n₂ m q hn1 hn2 hm hq hqlog hqmu
    (fun Ω => sampledColumnCountMax Ω)
    (fun Ω => sampled_column_count_max_nonnegative Ω)
    (hLD n₁ n₂ m hn1 hn2 hm)
