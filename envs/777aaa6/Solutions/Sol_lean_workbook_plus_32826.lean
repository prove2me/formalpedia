-- Prove2me | solution 1 for lean_workbook_plus_32826
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:56.006337+00:00
-- url     : https://prove2.me/submissions/ac87752c-be5f-4f3c-a398-e28a1e8e5600

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (x + z) * (y + z) ≥ (8:ℝ) / 9 * (x + y + z) * (x * y + x * z + y * z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
