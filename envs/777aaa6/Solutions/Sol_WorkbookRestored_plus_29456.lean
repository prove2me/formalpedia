-- Prove2me | solution 1 for WorkbookRestored.plus_29456
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:31.282551+00:00
-- url     : https://prove2.me/submissions/a31f3659-0a70-44fb-91b6-699d6bac1247

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_29456.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.logb 3 (90 - 3^4) * Real.logb 2 (76 - 44) * Real.logb 6 (1421 - 5^3) = 40   := by
  have h3 : logb 3 (90 - 3^4) = 2 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  have h2 : logb 2 (76 - 44) = 5 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  have h6 : logb 6 (1421 - 5^3) = 4 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  rw [h3,h2,h6]
  norm_num
#print axioms solution
