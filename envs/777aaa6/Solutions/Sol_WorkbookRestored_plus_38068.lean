-- Prove2me | solution 1 for WorkbookRestored.plus_38068
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:12.306505+00:00
-- url     : https://prove2.me/submissions/fd3e50ef-cd15-4558-aad4-677650098106

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_38068.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution {x : ℝ} (hx : 0 ≤ x) (a b : ℝ) : x ^ (a * b) = (x ^ a) ^ b   := by
  exact Real.rpow_mul hx a b
#print axioms solution
