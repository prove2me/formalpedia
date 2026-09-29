-- Prove2me | solution 1 for lean_workbook_plus_31219
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:00.385558+00:00
-- url     : https://prove2.me/submissions/e9f6b6b5-8e0c-48b9-9057-50de7c301f6b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) (h' : x^2 + y^2 + z^2 + x * y + x * z + y * z ≤ 1) : (1 - x) * (1 - y) * (1 - z) ≥ 9 * Real.sqrt 6 - 19 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
