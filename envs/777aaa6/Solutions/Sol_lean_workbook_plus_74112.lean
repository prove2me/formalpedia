-- Prove2me | solution 1 for lean_workbook_plus_74112
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:20.015889+00:00
-- url     : https://prove2.me/submissions/a41b4afe-2417-4abd-890e-5badf84d6481

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : x / (x + 1) + y / (y + 1) + z / (z + 1) ≤ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
