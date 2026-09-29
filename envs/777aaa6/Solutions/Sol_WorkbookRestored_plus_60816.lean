-- Prove2me | solution 1 for WorkbookRestored.plus_60816
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:07.651668+00:00
-- url     : https://prove2.me/submissions/04cbab67-df7e-45ec-8f61-3cdaf4f237d3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_60816.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : (exp x + 1) * (exp x + x + 1) = exp (2 * x) + (x + 2) * exp x + x + 1   := by
  simp [exp_add, exp_mul, add_mul, mul_add, mul_comm, mul_left_comm]
  ring
#print axioms solution
