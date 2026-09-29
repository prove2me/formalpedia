-- Prove2me | solution 1 for lean_workbook_plus_57488
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:27.103935+00:00
-- url     : https://prove2.me/submissions/5e532b32-df05-410f-ad7f-71dac4d8b083

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x*y*z = 1) : 2 * (x^4 + y^4 + z^4) + x^2*y^2 + y^2*z^2 + z^2*x^2 ≥ 3 * (x^3*y + y^3*z + z^3*x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
