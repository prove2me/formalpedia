-- Prove2me | solution 1 for lean_workbook_plus_15268
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:09.187252+00:00
-- url     : https://prove2.me/submissions/bc1851be-64aa-46d6-99c1-08dcbd002eb0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 3) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
