-- Prove2me | solution 2 for bernoulli_sampled_row_count_max_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-21T21:56:01.209652+00:00
-- url     : https://prove2.me/submissions/bd25158f-b5de-4251-ad71-e28f60316131

import Definitions.Def_matrix_completion_sampled_counts
import Theorems.Thm_bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
import Theorems.Thm_bernoulli_sampled_row_count_max_large_deviation_bound
import Theorems.Thm_sampled_row_count_max_nonnegative
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
              sampledRowCountMax Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  obtain ⟨Cdev, hCdev, hLD⟩ := bernoulli_sampled_row_count_max_large_deviation_bound
  obtain ⟨Cmoment, hCm, hmom⟩ :=
    bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound Cdev hCdev
  refine ⟨Cmoment, hCm, ?_⟩
  intro β hβ n₁ n₂ m q hn1 hn2 hm hq hqlog hqmu
  exact hmom β hβ n₁ n₂ m q hn1 hn2 hm hq hqlog hqmu
    (fun Ω => sampledRowCountMax Ω)
    (fun Ω => sampled_row_count_max_nonnegative Ω)
    (hLD n₁ n₂ m hn1 hn2 hm)
