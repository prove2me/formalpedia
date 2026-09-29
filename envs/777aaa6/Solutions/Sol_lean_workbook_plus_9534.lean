-- Prove2me | solution 1 for lean_workbook_plus_9534
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:13.2009+00:00
-- url     : https://prove2.me/submissions/e930a5a0-1324-4d5b-832e-21e5b66e5d9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  2 * (a^2 + b^2) ≥ (a + b)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
