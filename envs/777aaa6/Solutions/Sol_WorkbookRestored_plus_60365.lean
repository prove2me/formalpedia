-- Prove2me | solution 1 for WorkbookRestored.plus_60365
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:04.116281+00:00
-- url     : https://prove2.me/submissions/6d369a9e-1fef-45fa-b8eb-1b08b94e7462

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_60365.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (h : Real.cos (3 * x) = -1 / 2) :
  8 * (Real.cos x)^3 - 6 * Real.cos x + 1 = 0   := by
  linarith [cos_three_mul x]
#print axioms solution
