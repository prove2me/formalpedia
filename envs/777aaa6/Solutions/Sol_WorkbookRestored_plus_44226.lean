-- Prove2me | solution 1 for WorkbookRestored.plus_44226
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:08.195404+00:00
-- url     : https://prove2.me/submissions/5b9919ab-48a9-434f-a1bc-540414a89e98

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_44226.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : (5 * Real.logb 3 2) + (2 * Real.logb 9 10) = Real.logb 3 (2^6 * 5)   := by
  rw [show (2 : ℝ) = (2 : ℝ) by rfl, show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num, show (10 : ℝ) = (2 : ℝ) * (5 : ℝ) by norm_num]
  simp [logb, Real.log_mul, Real.log_rpow]
  ring
#print axioms solution
