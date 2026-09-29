-- Prove2me | solution 1 for WorkbookRestored.plus_1380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:41.694684+00:00
-- url     : https://prove2.me/submissions/3590cd7e-5779-4595-b02c-f79356328039

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_1380.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : 2 * (Real.sin (150 * π / 180) - Real.sin (80 * π / 180)) = 1 - 2 * Real.sin (80 * π / 180)   := by
  simp [sub_eq_add_neg, mul_add, mul_comm, mul_left_comm]
  rw [show (π : ℝ) * 150 / 180 = 5 * π / 6 by ring]
  rw [show (5 : ℝ) * π / 6 = π / 2 + π / 3 by ring]
  simp [add_mul, sin_add, sin_pi_div_two, cos_pi_div_three]
#print axioms solution
