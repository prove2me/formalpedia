-- Prove2me | solution 1 for lean_workbook_plus_70848
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:53:06.084803+00:00
-- url     : https://prove2.me/submissions/6534a26d-0451-4d24-ab11-1884945381cf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) : 2 * (x^2*y + y^2*z + z^2*x + x*y*z) ≥ (x + y) * (y + z) * (z + x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
