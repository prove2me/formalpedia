-- Prove2me | solution 1 for WorkbookRestored.plus_20863
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:38.353757+00:00
-- url     : https://prove2.me/submissions/0c3eacb8-cbee-44d6-adbe-aa501872b92b

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_20863.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c d : ℝ) : (Real.log b / Real.log a) * (Real.log d / Real.log c) = (Real.log b / Real.log c) * (Real.log d / Real.log a)   := by
  simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
#print axioms solution
