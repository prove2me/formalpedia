-- Prove2me | solution 1 for WorkbookRestored.plus_36143
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:51.700494+00:00
-- url     : https://prove2.me/submissions/ebdf8e31-39a7-40c8-92ed-36a03f9b6a27

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_36143.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a x : ℝ) (h₁ : x > 0) : a * Real.log x = Real.log (x ^ a)   := by
  rw [Real.log_rpow h₁]
#print axioms solution
