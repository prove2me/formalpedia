-- Prove2me | solution 1 for WorkbookRestored.plus_51901
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:46.70227+00:00
-- url     : https://prove2.me/submissions/b5373daf-19f7-4d31-86d6-b32b4cb69478

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51901.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x, -sinh (-x) = sinh x   := by
  exact fun x ↦ by simp [sinh_neg]
#print axioms solution
