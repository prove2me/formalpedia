-- Prove2me | solution 1 for WorkbookRestored.plus_51013
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:47.534601+00:00
-- url     : https://prove2.me/submissions/2c859bd1-c1aa-4df4-b339-f7948e118199

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51013.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  ∀ A B C : ℝ, (A + B + C = π ∧ A > 0 ∧ B > 0 ∧ C > 0 → (Real.tan (A / 2) + Real.tan (B / 2) + Real.tan (C / 2))^2 ≥ 3 * (Real.tan (A / 2) * Real.tan (B / 2) + Real.tan (B / 2) * Real.tan (C / 2) + Real.tan (C / 2) * Real.tan (A / 2)))   := by
  exact fun A B C h ↦ by linarith [sq_nonneg (tan (A / 2) - tan (B / 2)), sq_nonneg (tan (B / 2) - tan (C / 2)), sq_nonneg (tan (C / 2) - tan (A / 2))]
#print axioms solution
