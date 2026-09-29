-- Prove2me | solution 1 for WorkbookRestored.plus_25895
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:50.001082+00:00
-- url     : https://prove2.me/submissions/f483b904-01e5-4b0e-9525-107c941d819b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_25895.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (h : cos x - cos y = 1 / 5) :
  -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 1 / 5   := by
  rw [← sub_eq_zero] at h
  nlinarith [Real.cos_sub_cos x y, Real.cos_sub_cos (x + y) (x - y)]
#print axioms solution
