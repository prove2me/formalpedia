-- Prove2me | solution 1 for WorkbookRestored.plus_12099
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:06.93689+00:00
-- url     : https://prove2.me/submissions/d8863a20-9ef7-4e0d-b647-0d3f4f9aba3f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_12099.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : sin (50 * π / 180) = cos (40 * π / 180)   := by
  rw [← cos_pi_div_two_sub]
  ring_nf
#print axioms solution
