-- Prove2me | solution 2 for lean_workbook_plus_25229
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:59.651348+00:00
-- url     : https://prove2.me/submissions/ce02ab54-f543-4368-bb4d-1a1e737b4670

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x^2 + x*y + y^2 ≤ 3 * (x - Real.sqrt (x*y) + y)^2 := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x*y by positivity), Real.sqrt_nonneg (x*y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy])
