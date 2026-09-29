-- Prove2me | solution 1 for lean_workbook_plus_57464
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:23.491355+00:00
-- url     : https://prove2.me/submissions/28fd7d9c-bf89-4f00-8261-225d9ddfd83c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (4 * x + y + z) + y / (x + 4 * y + z) + z / (x + y + 4 * z) ≤ 1 / 2) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
