-- Prove2me | solution 1 for WorkbookRestored.plus_44985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:10.295415+00:00
-- url     : https://prove2.me/submissions/cf7a11d9-b7c4-4f1c-82e4-5d955f0a0bf4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_44985.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : |sin x| ≤ 1   := by
  exact abs_sin_le_one x
#print axioms solution
