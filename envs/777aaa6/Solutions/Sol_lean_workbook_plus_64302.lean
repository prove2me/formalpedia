-- Prove2me | solution 1 for lean_workbook_plus_64302
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:29.841165+00:00
-- url     : https://prove2.me/submissions/814745c7-792d-4b0f-9d69-549c78eb8c70

import Mathlib
set_option autoImplicit false

theorem solution  (f : ℝ → ℝ)
  (h₀ : ∀ x, ∀ y, f (x + y) = x + f y)
  (h₁ : f 0 = 2) :
  f 1998 = 2000   := by
  rw [← add_zero 1998]
  rw [h₀, h₁]
  norm_num

#print axioms solution
