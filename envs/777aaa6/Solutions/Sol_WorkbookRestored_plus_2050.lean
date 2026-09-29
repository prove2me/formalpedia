-- Prove2me | solution 1 for WorkbookRestored.plus_2050
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:48.047707+00:00
-- url     : https://prove2.me/submissions/719f5f8a-c2d6-4111-addf-24f407b63b45

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2050.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.log 5 / Real.log 3 * (Real.log 7 / Real.log 5) = Real.log 7 / Real.log 3   := by
  norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
#print axioms solution
