-- Prove2me | solution 1 for lean_workbook_plus_44294
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:39.70715+00:00
-- url     : https://prove2.me/submissions/8b303390-7046-46f9-bb5e-72d9a278d9e2

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ): (∀ x y : ℝ, (x + y) * (f x - f y) = (x - y) * (f x + f y)) ↔ ∃ a:ℝ, ∀ x : ℝ, f x = a * x   := by
  constructor
  intro h
  use f 1
  intro y
  linarith [h y 1]
  rintro ⟨a, ha⟩ x y
  rw [ha x, ha y]
  ring

#print axioms solution
