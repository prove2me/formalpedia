-- Prove2me | solution 2 for lean_workbook_plus_69459
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:47.038795+00:00
-- url     : https://prove2.me/submissions/d518d856-b97c-4032-a145-7afc5ebcb859

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hbc : b = c) : a^4 + 9 * a^2 * b^2 + 4 * b^4 ≥ 4 * a^3 * b + 10 * a * b^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
