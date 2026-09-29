-- Prove2me | solution 1 for WorkbookRestored.plus_59538
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:39.561699+00:00
-- url     : https://prove2.me/submissions/ae6605e2-a72b-414c-8d2c-fe67dc72e279

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_59538.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  padicValNat 2 (3^101 + 5^101) = 3   := by
  rw [padicValNat_def' (by decide) (by positivity)]
  apply multiplicity_eq_of_dvd_of_not_dvd <;> norm_num
#print axioms solution
