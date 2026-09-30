-- Prove2me | solution 1 for lean_workbook_plus_67605
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:29.762273+00:00
-- url     : https://prove2.me/submissions/c884a5cc-2efc-4811-a120-6726f834a2dc

import Mathlib
set_option autoImplicit false

theorem solution  (f : ℝ → ℝ)
  (h₀ : ∀ x, x ∈ Set.Icc 0 13 → f x = x^2 + x + 5) :
  f 13 = 187   := by
  rw [h₀ 13 (by norm_num)]
  norm_num

#print axioms solution
