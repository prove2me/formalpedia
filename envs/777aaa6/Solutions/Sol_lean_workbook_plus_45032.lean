-- Prove2me | solution 1 for lean_workbook_plus_45032
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:48.995844+00:00
-- url     : https://prove2.me/submissions/5cb22353-b7b1-4ba0-b153-0fda7ad66140

import Mathlib
set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (hf: f = fun (x:ℤ) ↦ x+1) : ∀ x y, f x * f y - f (x*y) = x + y   := by
  rw [hf]
  intro x y
  ring

#print axioms solution
