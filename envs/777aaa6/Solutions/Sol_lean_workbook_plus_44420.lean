-- Prove2me | solution 1 for lean_workbook_plus_44420
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:45.302741+00:00
-- url     : https://prove2.me/submissions/1af9aba0-d40d-4fb8-938d-aaad508f25bd

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / (a * (b + 1)) + 1 / (b * (a + 1)) = 1) : a + b + 1 ≥ 3 * a * b   := by
  have ha1 : a + 1 ≠ 0 := ne_of_gt (by linarith only [ha])
  have hb1 : b + 1 ≠ 0 := ne_of_gt (by linarith only [hb])
  field_simp [ne_of_gt ha, ne_of_gt hb, ha1, hb1] at hab
  have he : (a * b - 1) * (a + b + a * b) = 0 := by nlinarith only [hab]
  have hp : 0 < a + b + a * b := by positivity
  have hab1 : a * b = 1 := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt hp))
  have hs : 2 ≤ a + b := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt (add_pos ha hb))).mp
    nlinarith only [hab1, sq_nonneg (a - b)]
  nlinarith only [hab1, hs]

#print axioms solution
