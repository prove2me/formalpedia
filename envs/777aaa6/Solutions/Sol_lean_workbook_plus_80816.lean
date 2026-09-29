-- Prove2me | solution 1 for lean_workbook_plus_80816
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:44.264801+00:00
-- url     : https://prove2.me/submissions/ff91900b-32b8-4fb5-b459-0976f1acaaf5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ≥ (x * y + y * z + z * x)^2 / 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
