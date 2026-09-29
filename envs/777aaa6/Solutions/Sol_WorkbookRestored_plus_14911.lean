-- Prove2me | solution 1 for WorkbookRestored.plus_14911
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:16.138577+00:00
-- url     : https://prove2.me/submissions/34a5087e-e83a-4102-8ab6-86705bc24570

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_14911.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, x ∈ Set.Icc 0 (π / 2) ∧ y ∈ Set.Icc 0 (π / 2) → x < y → sin x < sin y ∧ cos y < cos x   := by
  rintro x y ⟨⟨hx0, hxπ⟩, ⟨hy0, hyπ⟩⟩ hxy
  rw [← sin_pi_div_two_sub, ← sin_pi_div_two_sub]
  constructor <;> apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith
#print axioms solution
