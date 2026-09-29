-- Prove2me | solution 1 for lean_workbook_plus_17710
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:12.478533+00:00
-- url     : https://prove2.me/submissions/315d6bba-7878-47e8-9a26-fbfa5fb524fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y) * (y + z) * (z + x) ≥ (x + 2 * y - z) * (y + 2 * z - x) * (z + 2 * x - y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz])
