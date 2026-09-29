-- Prove2me | solution 1 for lean_workbook_plus_78261
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:18.994928+00:00
-- url     : https://prove2.me/submissions/88b5b4b6-0fc4-4d4d-9e2f-862f6c9e858b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y + y * z + z * x ≤ x * y * z) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≥ 9 * (x * y + y * z + z * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
