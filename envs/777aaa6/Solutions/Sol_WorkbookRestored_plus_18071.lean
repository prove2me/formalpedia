-- Prove2me | solution 1 for WorkbookRestored.plus_18071
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:29.174058+00:00
-- url     : https://prove2.me/submissions/2c5b2fae-d185-4a3c-871c-79bc9e285142

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_18071.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, x ∈ Set.Ioo (-π / 2) (π / 2) ∧ y ∈ Set.Ioo (-π / 2) (π / 2) ∧ x < y → tan x < tan y   := by
  rintro x y ⟨h₁, h₂, h₃⟩
  apply tan_lt_tan_of_lt_of_lt_pi_div_two <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
#print axioms solution
