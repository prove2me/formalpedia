-- Prove2me | solution 1 for WorkbookRestored.plus_37102
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:53.297662+00:00
-- url     : https://prove2.me/submissions/9645ec46-6919-450d-87e1-32815d73674d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_37102.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c A : ℝ) : (b * Real.sin A * (a^2 + c^2 - b^2 - b^2 - c^2 + a^2)) / (2 * a * b * c) = (b * Real.sin A * (2 * a^2 - 2 * b^2)) / (2 * a * b * c)   := by
  ring
#print axioms solution
