-- Prove2me | solution 1 for lean_workbook_plus_1461
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:18.622422+00:00
-- url     : https://prove2.me/submissions/97b737fa-514d-433c-a599-1cbf56a72005

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^4 + y^4 + z^4 + x*y^3 + y*z^3 + z*x^3 ≥ 2*(x*y^3 + y*z^3 + z*x^3) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
