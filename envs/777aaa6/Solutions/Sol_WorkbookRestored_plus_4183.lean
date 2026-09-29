-- Prove2me | solution 1 for WorkbookRestored.plus_4183
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:22.962538+00:00
-- url     : https://prove2.me/submissions/827c6e12-74df-4e19-9e42-9735b5a6a7e1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_4183.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  Real.log 2 / Real.log 6 + Real.log 3 / Real.log 6 = 1   := by
  field_simp
  rw [← Real.log_mul] <;> norm_num [Real.log_pos_iff]
#print axioms solution
