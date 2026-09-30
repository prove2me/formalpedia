-- Prove2me | solution 2 for lean_workbook_plus_74676
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:27.745807+00:00
-- url     : https://prove2.me/submissions/0d26ae6c-a2b5-47fa-b9d5-f7d60e44d552

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (x + z) * (y + z) ≥ (8 / 9) * (x + y + z) * (x * y + x * z + y * z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
