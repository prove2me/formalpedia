-- Prove2me | solution 1 for lean_workbook_plus_78252
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:15.221221+00:00
-- url     : https://prove2.me/submissions/9e930430-55d6-47d0-9417-070948cde1fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^2 * y^2 + z^2 * y^2 + x^2 * z^2 ≤ x^4 + y^4 + z^4 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
