-- Prove2me | solution 1 for lean_workbook_plus_11271
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:55.504772+00:00
-- url     : https://prove2.me/submissions/beafdb97-6536-4f01-b855-45f024a46ebd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y z : ℝ) : (4 * z - 3 * y) ^ 2 - 5 * (5 * y ^ 2 + 5 * z ^ 2 - 8 * y * z) ≤ 0 := by
  (intros; nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (y - z), sq_nonneg (y + z)])
