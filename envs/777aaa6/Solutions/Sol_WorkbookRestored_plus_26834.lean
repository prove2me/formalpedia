-- Prove2me | solution 1 for WorkbookRestored.plus_26834
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:55.056185+00:00
-- url     : https://prove2.me/submissions/c23e99e1-9dc1-408c-b515-aa3ea4bf597f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_26834.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.tan (π / 3) = Real.sqrt 3   := by
  rw [Real.tan_pi_div_three]
#print axioms solution
