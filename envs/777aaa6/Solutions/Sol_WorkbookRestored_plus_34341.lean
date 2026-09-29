-- Prove2me | solution 1 for WorkbookRestored.plus_34341
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:48.81229+00:00
-- url     : https://prove2.me/submissions/7c74820b-c955-4d19-8d06-1fa9ca2dbbdb

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_34341.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → Real.logb a b + Real.logb a c = Real.logb a (b * c)   := by
  refine' fun a b c h => Eq.symm _
  rw [← Real.logb_mul (by linarith) (by linarith), mul_comm]
#print axioms solution
