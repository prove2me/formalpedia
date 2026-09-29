-- Prove2me | solution 1 for WorkbookRestored.plus_79397
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:32.125056+00:00
-- url     : https://prove2.me/submissions/33c031db-e590-4f4a-826a-166fa00c686c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_79397.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (hxy : x < y) (hx : 0 < x) (hy : 0 < y) : (2:ℝ)^x + (Real.log x) / (Real.log 2) < (2:ℝ)^y + (Real.log y) / (Real.log 2)   := by
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  gcongr
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxy
#print axioms solution
