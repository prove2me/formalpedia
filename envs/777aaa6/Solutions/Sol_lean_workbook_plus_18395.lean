-- Prove2me | solution 1 for lean_workbook_plus_18395
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:57:05.193408+00:00
-- url     : https://prove2.me/submissions/e7489bbd-d82c-483a-a6a6-9297207e52d1

import Mathlib.Analysis.SpecificLimits.Normed

theorem solution (t₁ : ℝ) (r : ℝ) (h : 0 < r) (h' : r < 1) :
    ∑' i : ℕ, t₁ * r ^ i = t₁ / (1 - r) := by
  have hr : |r| < 1 := by simpa [abs_of_pos h] using h'
  simpa [div_eq_mul_inv] using
    ((hasSum_geometric_of_abs_lt_one hr).mul_left t₁).tsum_eq

#print axioms solution
