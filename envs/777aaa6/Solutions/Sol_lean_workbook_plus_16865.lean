-- Prove2me | solution 1 for lean_workbook_plus_16865
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:17.304026+00:00
-- url     : https://prove2.me/submissions/cac4580c-3329-43ca-9d4c-17f0523b8591

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (2 / (x + y + z + 1) - 1 / (x + 1) / (y + 1) / (z + 1)) ≤ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz])
