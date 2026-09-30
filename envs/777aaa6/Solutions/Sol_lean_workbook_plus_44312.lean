-- Prove2me | solution 1 for lean_workbook_plus_44312
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:37.816214+00:00
-- url     : https://prove2.me/submissions/4d4d518c-b65a-4dfb-b38f-8e09aed2c1c0

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a^3 = 3*a*b^2 + 11) (h₂ : b^3 = 3*a^2*b + 2) : a^2 + b^2 = 5   := by
  have ha : a ^ 3 - 3 * a * b ^ 2 = 11 := by linarith only [h₁]
  have hb : b ^ 3 - 3 * a ^ 2 * b = 2 := by linarith only [h₂]
  have hc : (a ^ 2 + b ^ 2) ^ 3 = 125 := by
    calc
      (a ^ 2 + b ^ 2) ^ 3 = (a ^ 3 - 3 * a * b ^ 2) ^ 2 +
          (b ^ 3 - 3 * a ^ 2 * b) ^ 2 := by ring
      _ = 125 := by rw [ha, hb]; norm_num
  have hs : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hp : 0 < (a ^ 2 + b ^ 2) ^ 2 + 5 * (a ^ 2 + b ^ 2) + 25 := by positivity
  have he : (a ^ 2 + b ^ 2 - 5) * ((a ^ 2 + b ^ 2) ^ 2 + 5 * (a ^ 2 + b ^ 2) + 25) = 0 := by
    calc
      _ = (a ^ 2 + b ^ 2) ^ 3 - 125 := by ring
      _ = 0 := by rw [hc]; norm_num
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt hp))

#print axioms solution
