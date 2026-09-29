-- Prove2me | solution 1 for lean_workbook_plus_31520
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:18.864494+00:00
-- url     : https://prove2.me/submissions/a150627c-89e1-4295-a4b5-4446dc60e52f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a + b + c = 0) (hb : a * b + b * c + c * a = 3) (hc : a * b * c = -5) : a ^ 2 + b ^ 2 + c ^ 2 = -6 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
