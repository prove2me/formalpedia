-- Prove2me | solution 1 for WorkbookRestored.plus_27520
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:58.208935+00:00
-- url     : https://prove2.me/submissions/c688a9a7-1b17-4eb1-b2b5-68f6610877ac

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_27520.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) :
  Real.cos (3 * x) - Real.cos (5 * x) = 2 * Real.sin x * Real.sin (4 * x)   := by
  rw [cos_sub_cos]
  rw [show (3*x+5*x)/2 = 4*x by ring, show (3*x-5*x)/2 = -x by ring, sin_neg]
  ring
#print axioms solution
