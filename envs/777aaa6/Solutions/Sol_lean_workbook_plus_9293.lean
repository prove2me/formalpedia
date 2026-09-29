-- Prove2me | solution 1 for lean_workbook_plus_9293
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:01.021704+00:00
-- url     : https://prove2.me/submissions/1342e0a5-ee0d-40c4-a7dc-8817364efb09

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 2 * y) / (z + 2 * x + 3 * y) + (y + 2 * z) / (x + 2 * y + 3 * z) + (z + 2 * x) / (y + 2 * z + 3 * x) > 6 / 7 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
