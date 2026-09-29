-- Prove2me | solution 1 for WorkbookRestored.plus_28093
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:02:00.492452+00:00
-- url     : https://prove2.me/submissions/b44233ff-0079-4711-b3b1-c698422d8454

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_28093.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.sin (8 * π / 7) = -Real.sin (π / 7)   := by
  rw [← sin_pi_sub, ← sin_neg]
  ring_nf
#print axioms solution
