-- Prove2me | solution 1 for lean_workbook_plus_73842
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:17.522707+00:00
-- url     : https://prove2.me/submissions/7f25def8-03fe-41fc-b6b8-b5d700757a25

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≤ (3 * (x + y + z)) / (2 * (x*y + y*z + z*x)) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
