-- Prove2me | solution 1 for lean_workbook_plus_56784
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:53.040439+00:00
-- url     : https://prove2.me/submissions/dd5725b9-adc4-490b-b275-cdb70d21f663

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 4*x^4 + 4*y^4 ≥ x^3*y + 6*x^2*y^2 + x*y^3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
