-- Prove2me | solution 1 for lean_workbook_plus_78817
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:24.830146+00:00
-- url     : https://prove2.me/submissions/2e90db4d-9c6c-4087-b95d-631ea65dba1d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : 3 / 2 ≤ x / (y + z) + y / (x + z) + z / (x + y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
