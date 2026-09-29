-- Prove2me | solution 1 for WorkbookRestored.plus_15056
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:17.549977+00:00
-- url     : https://prove2.me/submissions/69e9adac-7c19-46cc-a5fa-dc6517eb4349

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_15056.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, 0 ≤ (1 - Real.sin x) * (1 - Real.sin y)   := by
  exact fun x y ↦ mul_nonneg (sub_nonneg.2 (sin_le_one x)) (sub_nonneg.2 (sin_le_one y))
#print axioms solution
