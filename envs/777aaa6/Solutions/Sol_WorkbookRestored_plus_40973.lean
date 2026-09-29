-- Prove2me | solution 1 for WorkbookRestored.plus_40973
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:01.597861+00:00
-- url     : https://prove2.me/submissions/6d85e4fe-3adf-4b5c-a466-7812a24be8a5

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_40973.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : x^2 - x * (sin x + cos x) + sin x * cos x = (x - sin x) * (x - cos x)   := by
  ring
#print axioms solution
