-- Prove2me | solution 1 for lean_workbook_plus_81939
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T14:28:18.540919+00:00
-- url     : https://prove2.me/submissions/68967e42-6592-4db0-bef2-de985149a5c0

import Mathlib.Tactic

theorem solution (a b : ℝ) (h₀ : a + b = 10) (h₁ : a * b = 20) : 1 / a + 1 / b = 1 / 2 := by
  have hab : a * b ≠ 0 := by rw [h₁]; norm_num
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb : b ≠ 0 := right_ne_zero_of_mul hab
  field_simp [ha, hb]
  linarith
