-- Prove2me | solution 1 for lean_workbook_plus_56290
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:32.527899+00:00
-- url     : https://prove2.me/submissions/5d2eb1b1-1edd-4a1c-bc9a-e12621c04ce5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z)) ≤ 3 / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
