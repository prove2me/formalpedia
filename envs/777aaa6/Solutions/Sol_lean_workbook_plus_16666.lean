-- Prove2me | solution 1 for lean_workbook_plus_16666
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:38.886828+00:00
-- url     : https://prove2.me/submissions/cdf40ebd-6cbd-48aa-ab66-90e5373fbc46

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
