-- Prove2me | solution 1 for lean_workbook_plus_46622
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:14:43.635153+00:00
-- url     : https://prove2.me/submissions/00f0617a-2af3-444a-81c3-d454bae27e0e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ 8 / 9 * (x + y + z) * (x * y + y * z + z * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
