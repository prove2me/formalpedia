-- Prove2me | solution 1 for WorkbookRestored.plus_3527
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:25.304005+00:00
-- url     : https://prove2.me/submissions/8e26b3d2-e66d-4908-80c0-dc12b479a19d

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_3527.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  x^(1/x) ≤ x^x   := by
  apply Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le
  apply (le_div_iff₀ hx.1).2
  nlinarith [mul_pos hx.1 (sub_pos.mpr hx.2)]
#print axioms solution
