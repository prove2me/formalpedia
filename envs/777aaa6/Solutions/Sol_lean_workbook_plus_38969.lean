-- Prove2me | solution 1 for lean_workbook_plus_38969
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:27.684268+00:00
-- url     : https://prove2.me/submissions/43b61f03-0e82-496b-88d7-33395093326a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : (x + y + z + t) ^ 3 ≥ 16 * (x*y*z + y*z*t + z*t*x + t*x*y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t), sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + t), sq_nonneg (y + z), sq_nonneg (y + t), sq_nonneg (z + t), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
