-- Prove2me | solution 1 for lean_workbook_plus_6806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:30.50533+00:00
-- url     : https://prove2.me/submissions/c6e03f08-15c4-4d29-ae23-23345e4c7922

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (n : ℤ) (a : ℝ) (h₁ : n = Int.floor x) (h₂ : a = x - n) : 0 ≤ a ∧ a < 1   := by
  rw [h₂, h₁]
  refine' ⟨by linarith [Int.floor_le x], by linarith [Int.lt_floor_add_one x]⟩

#print axioms solution
