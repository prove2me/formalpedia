-- Prove2me | solution 1 for WorkbookRestored.plus_12215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:08.605168+00:00
-- url     : https://prove2.me/submissions/0272040a-d561-4374-8156-b9d4150859ae

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_12215.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : sin (π / 2) = 1   := by
  simp [Real.sin_pi_div_two]
#print axioms solution
