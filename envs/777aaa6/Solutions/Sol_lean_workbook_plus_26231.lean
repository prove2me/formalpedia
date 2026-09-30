-- Prove2me | solution 1 for lean_workbook_plus_26231
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:15.64483+00:00
-- url     : https://prove2.me/submissions/f04eebff-6591-4a71-b047-ccbc6bf866d6

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x / (2 * y + 9) + y / (3 * x + 6) + 3 / (2 * x + 3 * y)) ≥ 3 / 5 := by
  have h1 : 0 < 2 * y + 9 := by linarith
  have h2 : 0 < 3 * x + 6 := by linarith
  have h3 : 0 < 2 * x + 3 * y := by linarith
  rw [ge_iff_le, div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ (by positivity) h3.ne',
    div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y), mul_pos hx hy,
    mul_pos (mul_pos hx hy) hx, mul_pos (mul_pos hx hy) hy, sq_nonneg (x + y - 6),
    mul_nonneg hx.le (sq_nonneg (x - 3)), mul_nonneg hy.le (sq_nonneg (y - 3)),
    mul_nonneg hx.le (sq_nonneg (y - 3)), mul_nonneg hy.le (sq_nonneg (x - 3)),
    mul_nonneg hx.le (sq_nonneg (x - y)), mul_nonneg hy.le (sq_nonneg (x - y))]
