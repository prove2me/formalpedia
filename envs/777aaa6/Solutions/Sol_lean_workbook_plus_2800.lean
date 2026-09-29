-- Prove2me | solution 1 for lean_workbook_plus_2800
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:09.325918+00:00
-- url     : https://prove2.me/submissions/8e8d83af-a95a-4a9a-9a21-dd631446c22c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) : (a + b) * (b + c) * (c + a) / 8 ≤ (a + b + c) ^ 3 / 27 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
