-- Prove2me | solution 1 for WorkbookRestored.plus_51434
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:48.229609+00:00
-- url     : https://prove2.me/submissions/aa155745-9195-469f-a2b1-7f9b1ce98818

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51434.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a^(Real.log c / Real.log b) = c^(Real.log a / Real.log b)   := by
  simp [← rpow_mul, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hc,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
#print axioms solution
