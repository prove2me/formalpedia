-- Prove2me | solution 1 for lean_workbook_plus_2319
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:20:58.099364+00:00
-- url     : https://prove2.me/submissions/f8bda9c6-e505-4143-ae6d-0a640cbd1b18

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (hx : 1 < x) (hy : 1 < y) : (x^2 / (y - 1) + y^2 / (x - 1)) ≥ 8 := by
  have hx' : 0 < x - 1 := by linarith
  have hy' : 0 < y - 1 := by linarith
  rw [ge_iff_le, div_add_div _ _ hy'.ne' hx'.ne', le_div_iff₀ (mul_pos hy' hx')]
  nlinarith [mul_nonneg (sq_nonneg (x - 2)) hx'.le, mul_nonneg (sq_nonneg (y - 2)) hy'.le,
    sq_nonneg (x - y), mul_pos hx' hy']
