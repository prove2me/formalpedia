-- Prove2me | solution 1 for lean_workbook_plus_63237
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:30.233882+00:00
-- url     : https://prove2.me/submissions/645f4542-fddc-4c74-8504-35a15b3d8baf

import Mathlib
set_option autoImplicit false

theorem solution  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x * y = 9)
  (h₂ : 1 / x = 4 * (1 / y)) :
  x + y = 15 / 2   := by
  field_simp [ne_of_gt h₀.1, ne_of_gt h₀.2] at h₂
  have hx : x = 3 / 2 := by nlinarith [h₁, h₀.1]
  nlinarith [h₁, h₂]

#print axioms solution
