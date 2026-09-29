-- Prove2me | solution 1 for lean_workbook_plus_32106
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:53.427865+00:00
-- url     : https://prove2.me/submissions/d950ebe1-9510-4b4a-b887-ad72985727cf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : (x + 1) ^ 3 + (y + 1) ^ 3 + (z + 1) ^ 3 - 3 * x * y * z = 1): x + y + z ≤ -1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
