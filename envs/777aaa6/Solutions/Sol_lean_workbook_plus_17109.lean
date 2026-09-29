-- Prove2me | solution 1 for lean_workbook_plus_17109
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:44.304767+00:00
-- url     : https://prove2.me/submissions/11908af8-af4f-44de-acb0-d22f7030089b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : 1 / (x ^ 2 + x + 1) + 1 / (y ^ 2 + y + 1) + 1 / (z ^ 2 + z + 1) >= 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
