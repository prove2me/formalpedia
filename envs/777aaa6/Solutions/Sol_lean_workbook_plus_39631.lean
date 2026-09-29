-- Prove2me | solution 1 for lean_workbook_plus_39631
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:25.376411+00:00
-- url     : https://prove2.me/submissions/31063d63-0f64-4b21-8f65-9166a05a9f4a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2 * (y + z) + y^2 * (x + z) + z^2 * (x + y) >= 6 * x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
