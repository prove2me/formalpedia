-- Prove2me | solution 2 for lean_workbook_plus_54255
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:59.327125+00:00
-- url     : https://prove2.me/submissions/2742474f-b96e-4542-bc80-f32e9c3ed761

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 / (x + y) + y^2 / (y + z) + z^2 / (z + x)) ≥ (x + y + z) / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
