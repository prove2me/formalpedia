-- Prove2me | solution 1 for lean_workbook_plus_33925
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:48.966048+00:00
-- url     : https://prove2.me/submissions/ac0ebbd6-ce57-4a14-8ae1-bf9e32bb25e5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x / (2 * x + y + z) + y / (2 * y + z + x) + z / (2 * z + x + y) ≤ 3 / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
