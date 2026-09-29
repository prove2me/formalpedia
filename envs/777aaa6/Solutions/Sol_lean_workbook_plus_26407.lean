-- Prove2me | solution 1 for lean_workbook_plus_26407
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:47.891629+00:00
-- url     : https://prove2.me/submissions/c2b1b2c0-c474-4098-ac8e-6fed6d630194

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 0) : x^3 + y^3 + z^3 = 3 * x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
