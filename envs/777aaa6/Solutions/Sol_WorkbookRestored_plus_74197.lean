-- Prove2me | solution 1 for WorkbookRestored.plus_74197
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:25.250357+00:00
-- url     : https://prove2.me/submissions/0df2edf5-f392-4d57-b1e6-6eedf5903340

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_74197.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) : sin (a - b) = sin a * cos b - sin b * cos a   := by
  simp [sub_eq_add_neg, sin_add, cos_neg, mul_comm]
#print axioms solution
