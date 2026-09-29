-- Prove2me | solution 1 for binomial_lower_tail_at_matrix_sample_mean_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T03:21:54.151728+00:00
-- url     : https://prove2.me/submissions/f9e283fb-b32f-4c40-9a60-bc4030a837e6

import Theorems.Thm_binomial_lower_tail_at_integer_mean_ge_half
import Definitions.Def_matrix_completion_fixed_cardinality

open MatrixCompletion

theorem solution
    (n₁ n₂ m : ℕ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (1 / 2 : ℝ) ≤
        binomialLowerTailProb (n₁ * n₂) m
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  intro _ _ hm
  have h := binomial_lower_tail_at_integer_mean_ge_half (n₁ * n₂) m hm
  simpa [Nat.cast_mul] using h
