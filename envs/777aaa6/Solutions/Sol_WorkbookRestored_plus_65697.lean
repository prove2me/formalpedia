-- Prove2me | solution 1 for WorkbookRestored.plus_65697
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:13.669129+00:00
-- url     : https://prove2.me/submissions/c3cb893c-a591-46bd-aa7a-5762b1673c7c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_65697.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.sin (8 * Real.pi / 17) = Real.cos (Real.pi / 34)   := by
  rw [show (8 : ℝ) * π / 17 = π / 2 - π / 34 by ring, sin_pi_div_two_sub]
#print axioms solution
