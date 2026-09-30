-- Prove2me | solution 2 for lean_workbook_plus_45770
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:40:30.87518+00:00
-- url     : https://prove2.me/submissions/908b58c3-cd9c-4cfc-95ee-7ef4ead8fabb

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h₁ : 0 < y ∧ y ≤ x ∧ x ≤ 2) (h₂ : x * y ^ 2 ≤ 2) : x + 2 * y ≤ 4 := by
  obtain ⟨hy, hyx, hx2⟩ := h₁
  by_contra hcon
  push_neg at hcon
  -- y > 1 and y^3 ≤ 2
  have hy1 : 1 < y := by linarith
  have hy3 : y ^ 3 ≤ 2 := by nlinarith [mul_le_mul_of_nonneg_right hyx (sq_nonneg y)]
  -- x > 4 - 2y, so 2 ≥ x y^2 > (4 - 2y) y^2
  have hk : (4 - 2 * y) * y ^ 2 < x * y ^ 2 := by
    apply mul_lt_mul_of_pos_right _ (by positivity)
    linarith
  -- (4 - 2y) y^2 - 2 = -2 (y-1)(y^2 - y - 1) ≥ 0 when 1 < y ≤ 2^(1/3)
  have hq : y ^ 2 - y - 1 < 0 := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr hy1) (neg_pos.mpr hq)]
