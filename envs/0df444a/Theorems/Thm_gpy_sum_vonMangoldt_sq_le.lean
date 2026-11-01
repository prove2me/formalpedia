-- Prove2me | Theorems.Thm_gpy_sum_vonMangoldt_sq_le
-- name    : gpy_sum_vonMangoldt_sq_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T05:05:21.742176+00:00
-- url     : https://prove2.me/theorems/f5e63d63-cb9d-4ca7-a687-a9a4a5296dd8
-- title:
--   Diagonal second moment of the von Mangoldt function
-- statement:
--   Unconditional elementary input: the diagonal second moment of the von Mangoldt function, sum over n up to N of Lambda(n) squared, is at most (log 4 + 4) times N times log N, from Lambda(n) at most log n and Mathlib's Chebyshev psi bound. This is one analytic input a large-sieve proof of BDH would consume; it is not BDH itself.
-- source:
--   GPY genuine-BDH conditional reduction (GPYBDHFull.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_sum_vonMangoldt_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt n) ^ 2 ≤
      (Real.log 4 + 4) * (N : ℝ) * Real.log (N : ℝ) := by sorry
