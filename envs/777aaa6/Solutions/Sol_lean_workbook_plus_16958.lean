-- Prove2me | solution 1 for lean_workbook_plus_16958
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:17.350442+00:00
-- url     : https://prove2.me/submissions/202650f6-97d3-4549-bc2d-cd3ee5b36181

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a + b) ^ 2 - 3 * a * b ≥ (a + b) ^ 2 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
