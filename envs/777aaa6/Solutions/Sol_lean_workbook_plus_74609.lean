-- Prove2me | solution 1 for lean_workbook_plus_74609
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:24.410034+00:00
-- url     : https://prove2.me/submissions/005e2187-61f5-4901-b20f-8e0ca5c93d0b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : (x / (x + y + z + t) + (x + y) / (x + y + z)) > 2 * (2 * x + y) / (2 * x + 2 * y + 2 * z + t) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t), sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + t), sq_nonneg (y + z), sq_nonneg (y + t), sq_nonneg (z + t), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
