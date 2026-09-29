-- Prove2me | solution 1 for lean_workbook_plus_13420
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:53.104728+00:00
-- url     : https://prove2.me/submissions/aff40c47-72b7-403c-a0aa-ed59490d7e30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * (x + y) ^ 2 * z + 2 * (y + z) ^ 2 * x + 2 * (z + x) ^ 2 * y ≤ 3 * (x + y) * (y + z) * (z + x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
