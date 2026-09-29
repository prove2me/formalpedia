-- Prove2me | solution 1 for WorkbookRestored.plus_35485
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:50.329018+00:00
-- url     : https://prove2.me/submissions/b4c0a948-193d-458f-bd7b-b8d443685fba

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_35485.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (p y : ℝ) (h₁ : y = 2 * Real.sin p) (h₂ : -Real.pi / 2 ≤ p ∧ p ≤ Real.pi / 2) : -2 ≤ y ∧ y ≤ 2   := by
  refine ⟨?_,?_⟩ <;> linarith [sin_le_one p, neg_one_le_sin p, h₁, h₂.1, h₂.2]
#print axioms solution
