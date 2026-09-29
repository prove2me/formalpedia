-- Prove2me | solution 1 for lean_workbook_plus_56623
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:29.651929+00:00
-- url     : https://prove2.me/submissions/1097bc1a-046a-4ede-9904-bcb7b21b9599

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (ha : a>0) (hb : b>0) (hc : c>0) : a^2 + b^2 + c^2 >= a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
