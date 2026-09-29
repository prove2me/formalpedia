-- Prove2me | solution 1 for lean_workbook_plus_64497
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:11:15.166667+00:00
-- url     : https://prove2.me/submissions/9471d4d8-8257-4287-8156-bd6f758502a7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option autoImplicit false
theorem solution : ∃ f : ℚ → ℝ, ∀ x y : ℚ, x > 0 ∧ y > 0 → f (x * y) = f x * f y   :=  by
  exact ⟨fun _ => 1, by simp⟩
#print axioms solution
