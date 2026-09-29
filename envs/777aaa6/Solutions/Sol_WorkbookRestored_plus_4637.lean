-- Prove2me | solution 1 for WorkbookRestored.plus_4637
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:03.835108+00:00
-- url     : https://prove2.me/submissions/0b4900ed-66da-4c7e-aede-e870e2b620de

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_4637.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  -(1 / 2) * (Real.cos 1 - Real.cos 0) = (1 - Real.cos 1) / 2   := by
  rw [Real.cos_zero]
  ring
#print axioms solution
