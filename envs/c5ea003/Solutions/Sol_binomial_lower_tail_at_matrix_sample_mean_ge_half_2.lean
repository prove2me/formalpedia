-- Prove2me | solution 2 for binomial_lower_tail_at_matrix_sample_mean_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:19:46.435357+00:00
-- url     : https://prove2.me/submissions/0b785247-4a50-4252-97e3-d0f67df728e6

import Theorems.Thm_binomial_lower_tail_at_integer_mean_ge_half

open MatrixCompletion

/-- Specialize the integer-mean binomial lower-tail theorem to
`N = n₁ * n₂`, rewriting the matrix sample ratio into that form. -/
theorem solution
    (n₁ n₂ m : ℕ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (1 / 2 : ℝ) ≤
        binomialLowerTailProb (n₁ * n₂) m
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  intro _hn₁ _hn₂ hm
  simpa [Nat.cast_mul] using
    binomial_lower_tail_at_integer_mean_ge_half (n₁ * n₂) m hm

