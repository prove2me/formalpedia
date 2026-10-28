-- Prove2me | Theorems.Thm_gpy_sum_tau_le
-- name    : gpy_sum_tau_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:18:36.82899+00:00
-- url     : https://prove2.me/theorems/30f9b911-2e1d-4b02-9f55-4cc1f68a79ac
-- title:
--   Divisor summatory bound: sum of τ up to R
-- statement:
--   For R ≥ 1, the sum of the divisor-count function τ(D) over 1 ≤ D ≤ R is at most R·(1 + log R). The bound is proved by double counting: summing τ(D) over D ≤ R counts pairs (d, D) with d dividing D, which regroups as the sum over d ≤ R of the number of multiples of d up to R, combined with the harmonic bound ∑_{d ≤ R} 1/d ≤ 1 + log R.
-- source:
--   GPY τ-moment / divisor-sum estimates for Selberg weights, formalized from Mathlib (divisor double count, harmonic bound, divisor convolution, and the τ-weighted λ-mass identity)

import Mathlib
open Classical

theorem gpy_sum_tau_le {R : ℕ} (hR : 1 ≤ R) :
    (∑ D ∈ Finset.Icc 1 R, ((Nat.divisors D).card : ℝ)) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) := by sorry
