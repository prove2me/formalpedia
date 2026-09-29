-- Prove2me | solution 1 for WorkbookRestored.plus_29613
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:32.381069+00:00
-- url     : https://prove2.me/submissions/3c9e6f43-f045-424a-8e2a-b2cf2d62cfba

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_29613.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (L : ℝ) : L * (1 - exp (-L^2 / 4)) = 0 ↔ L = 0   := by
  simp [exp_ne_zero, sub_eq_zero]
  simp [Real.exp_mul, exp_neg, neg_div, mul_div_cancel_left]
#print axioms solution
