-- Prove2me | solution 1 for lean_workbook_plus_6915
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:21.29782+00:00
-- url     : https://prove2.me/submissions/823561a1-03aa-4b6d-b37f-97780c6cfe01

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) < 5 / 2   := by
  intro a b c h
  rcases h with ⟨ha, hb, hc⟩
  have hab : 0 < a + 2 * b := by positivity
  have hbc : 0 < b + 2 * c := by positivity
  have hca : 0 < c + 2 * a := by positivity
  have hs : 0 < 2 * (a + b + c) := by positivity
  have h1 : b / (2 * (a + b + c)) < b / (a + 2 * b) :=
    div_lt_div_of_pos_left hb hab (by linarith)
  have h2 : c / (2 * (a + b + c)) < c / (b + 2 * c) :=
    div_lt_div_of_pos_left hc hbc (by linarith)
  have h3 : a / (2 * (a + b + c)) < a / (c + 2 * a) :=
    div_lt_div_of_pos_left ha hca (by linarith)
  have ht : b / (2 * (a + b + c)) + c / (2 * (a + b + c)) +
      a / (2 * (a + b + c)) = (1 : ℝ) / 2 := by
    field_simp [ne_of_gt hs]
    ring
  have e1 : (a + b) / (a + 2 * b) = 1 - b / (a + 2 * b) := by
    field_simp [ne_of_gt hab]
    ring
  have e2 : (b + c) / (b + 2 * c) = 1 - c / (b + 2 * c) := by
    field_simp [ne_of_gt hbc]
    ring
  have e3 : (c + a) / (c + 2 * a) = 1 - a / (c + 2 * a) := by
    field_simp [ne_of_gt hca]
    ring
  rw [e1, e2, e3]
  linarith only [h1, h2, h3, ht]

#print axioms solution
