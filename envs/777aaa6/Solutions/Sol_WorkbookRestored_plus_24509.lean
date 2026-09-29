-- Prove2me | solution 1 for WorkbookRestored.plus_24509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:55.016356+00:00
-- url     : https://prove2.me/submissions/74f13488-ac6e-461a-88df-b95539f8a2bf

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_24509. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 1 < x) : x^(1/x) ≤ x^x   := by
  apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hx)
  apply (div_le_iff₀ (by linarith : 0 < x)).2
  nlinarith
#print axioms solution
