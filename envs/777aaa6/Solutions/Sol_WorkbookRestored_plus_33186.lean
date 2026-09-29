-- Prove2me | solution 1 for WorkbookRestored.plus_33186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:42.022525+00:00
-- url     : https://prove2.me/submissions/182468c3-d991-4192-8513-316c46525508

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33186.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (c : ℝ) : 0 < exp (c * x)   := by
  exact Real.exp_pos _
#print axioms solution
