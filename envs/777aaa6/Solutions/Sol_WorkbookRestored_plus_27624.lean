-- Prove2me | solution 1 for WorkbookRestored.plus_27624
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:59.007068+00:00
-- url     : https://prove2.me/submissions/c31d7ba8-9f63-42e8-8ac2-da67080616cb

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_27624.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : (Real.logb 2 3) * (Real.logb 3 4) * (Real.logb 4 5) * (Real.logb 5 6) = Real.logb 2 6   := by
  norm_num [logb, div_eq_inv_mul, mul_comm, mul_assoc, mul_left_comm]
#print axioms solution
