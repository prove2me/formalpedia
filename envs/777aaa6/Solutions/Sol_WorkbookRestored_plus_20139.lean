-- Prove2me | solution 1 for WorkbookRestored.plus_20139
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:36.240333+00:00
-- url     : https://prove2.me/submissions/21109745-7b40-4294-a855-191099bd1600

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_20139.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, x > 0 ∧ y > 0 → Real.log x + Real.log y = Real.log (x*y)   := by
  refine' fun x y h => by rw [log_mul h.1.ne' h.2.ne', add_comm]
#print axioms solution
