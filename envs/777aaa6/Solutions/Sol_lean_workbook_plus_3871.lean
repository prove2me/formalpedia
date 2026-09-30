-- Prove2me | solution 1 for lean_workbook_plus_3871
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:56.808362+00:00
-- url     : https://prove2.me/submissions/57e8c56d-7336-4a6b-9e18-433baacf2a05

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) / (x + y + 1) ≤ x / (x + 1) + y / (y + 1) ∧ x / (x + 1) + y / (y + 1) ≤ (2 * (x + y)) / (x + y + 2) := by
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  have hxy1 : 0 < x + y + 1 := by linarith
  have hxy2 : 0 < x + y + 2 := by linarith
  have hsum : x / (x + 1) + y / (y + 1) = (x * (y + 1) + (x + 1) * y) / ((x + 1) * (y + 1)) := by
    rw [div_add_div _ _ hx1.ne' hy1.ne']
  rw [hsum]
  constructor
  · rw [div_le_div_iff₀ hxy1 (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hx hy) (add_nonneg hx hy), mul_nonneg hx hy]
  · rw [div_le_div_iff₀ (by positivity) hxy2]
    nlinarith [sq_nonneg (x - y)]
