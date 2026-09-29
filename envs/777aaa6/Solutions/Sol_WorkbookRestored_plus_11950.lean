-- Prove2me | solution 1 for WorkbookRestored.plus_11950
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:04.977513+00:00
-- url     : https://prove2.me/submissions/94ef17a7-35f4-4978-b226-ddb7a608ec21

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_11950.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution x : Real.cos (3 * x) = Real.cos x * (1 - 4 * (Real.sin x)^2)   := by
  rw [Real.cos_three_mul, sin_sq, mul_sub, mul_one]
  ring
#print axioms solution
