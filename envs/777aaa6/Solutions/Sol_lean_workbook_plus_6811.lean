-- Prove2me | solution 1 for lean_workbook_plus_6811
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:19.190411+00:00
-- url     : https://prove2.me/submissions/040b3b18-5047-4bf7-9381-6c994b07e646

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  x^2 * y^2 - x^2 * y * z + x^2 * z^2 - x * y^2 * z - x * y * z^2 + y^2 * z^2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
