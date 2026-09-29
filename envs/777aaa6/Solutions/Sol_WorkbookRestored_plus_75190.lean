-- Prove2me | solution 1 for WorkbookRestored.plus_75190
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:26.904321+00:00
-- url     : https://prove2.me/submissions/d9420b57-9cce-40b8-85dd-13ee493a9e6b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_75190.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : tan (π/2 - x) = 1 / tan x   := by
  simp [tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
#print axioms solution
