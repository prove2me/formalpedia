-- Prove2me | solution 1 for WorkbookRestored.plus_23480
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:43.336603+00:00
-- url     : https://prove2.me/submissions/82cecd42-349e-4be6-9a69-28aa4fc8eb66

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_23480.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.logb 4 8 = 3 / 2   := by
  norm_num [logb_eq_iff_rpow_eq, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
#print axioms solution
