-- Prove2me | Theorems.Thm_gpy_abel_sum
-- name    : gpy_abel_sum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:10:07.815473+00:00
-- url     : https://prove2.me/theorems/d0ba43b2-c2ea-4e28-8f55-a625244006df
-- title:
--   Abel summation by parts
-- statement:
--   Let a and f be real sequences. For every n, the weighted sum sum_{i<=n} a_i * f_i equals the partial sum sum_{i<=n} a_i times f_n, minus the sum over i < n of the partial sum sum_{j<=i} a_j times the weight difference f_{i+1} - f_i. This is summation by parts, the discrete analogue of integration by parts.
-- source:
--   GPY monomial-sum evaluation: summation by parts for real sequences, the discrete engine for mu-weighted log-power sums

import Mathlib
open Classical

theorem gpy_abel_sum (a f : ℕ → ℝ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (n + 1), a i * f i
      = (∑ i ∈ Finset.range (n + 1), a i) * f n
        - ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i) := by sorry
