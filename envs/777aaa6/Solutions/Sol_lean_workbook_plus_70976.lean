-- Prove2me | solution 1 for lean_workbook_plus_70976
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:17.036701+00:00
-- url     : https://prove2.me/submissions/a9d54fa4-87ba-4e98-8476-809dbe4d6c7a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) : (p + q + r) ^ 3 ≥ 27 * p * q * r := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (r), sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r), sq_nonneg (p + q), sq_nonneg (p + r), sq_nonneg (q + r), mul_nonneg hp hq, mul_nonneg hp hr, mul_nonneg hq hr])
