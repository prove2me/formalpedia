-- Prove2me | solution 1 for WorkbookRestored.plus_60336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:02.977783+00:00
-- url     : https://prove2.me/submissions/c0f8a98b-1c16-4d56-953f-aee7c66c8d0f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_60336.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.cos (36 * Real.pi / 180) - Real.cos (72 * Real.pi / 180) = Real.sin (54 * Real.pi / 180) - Real.sin (18 * Real.pi / 180)   := by
  rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub]
  ring_nf
#print axioms solution
