-- Prove2me | solution 1 for lean_workbook_plus_49250
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:45.522642+00:00
-- url     : https://prove2.me/submissions/245795b2-9527-438c-b139-18d894effada

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 4 / (x ^ 2 + y * z) ≤ 1 / (x * y) + 1 / (x * z) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
