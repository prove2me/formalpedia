-- Prove2me | solution 1 for lean_workbook_plus_78157
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:05.144837+00:00
-- url     : https://prove2.me/submissions/d0e97a7a-e409-4021-9182-ba0b1b7e779e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℝ) : (p * q) ^ 2 - (p + q) ^ 2 + 6 * p * q + 3 * (p ^ 2 + q ^ 2) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (p - q), sq_nonneg (p + q)])
