-- Prove2me | solution 1 for WorkbookRestored.plus_54215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:52.536981+00:00
-- url     : https://prove2.me/submissions/30b6c75c-2847-4932-a75b-85d23ae2617d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_54215.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) : Real.sin (4 * a) = 4 * Real.sin a * (Real.cos a)^3 - 4 * Real.cos a * (Real.sin a)^3   := by
  rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, sin_two_mul]
  simp [two_mul, sin_add, cos_add, cos_two_mul, sin_two_mul]
  ring
#print axioms solution
