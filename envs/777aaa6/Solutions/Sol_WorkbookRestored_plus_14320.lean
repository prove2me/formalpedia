-- Prove2me | solution 1 for WorkbookRestored.plus_14320
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:13.071359+00:00
-- url     : https://prove2.me/submissions/d532de7d-c5c4-435d-96ef-2f3f17d506fd

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_14320.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : tan (π / 4) = 1   := by
  simp [tan_eq_sin_div_cos, sin_pi_div_four, cos_pi_div_four]
#print axioms solution
