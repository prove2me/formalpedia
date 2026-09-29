-- Prove2me | solution 1 for WorkbookRestored.plus_20381
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:37.636395+00:00
-- url     : https://prove2.me/submissions/b97151fb-61a6-462d-943d-3f61092d6f09

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_20381.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : tan (π / 2 + π / 4) = -1   := by
  simp [tan_eq_sin_div_cos, sin_add, cos_add, sin_pi_div_four, cos_pi_div_four]
#print axioms solution
