-- Prove2me | solution 1 for WorkbookRestored.plus_26955
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:55.772975+00:00
-- url     : https://prove2.me/submissions/373bbaf4-cb96-4b67-b11b-5eda0ec55e92

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_26955.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (x : ℝ) : (sin (n * x))^2 = 1 / 2 * (1 - cos (2 * n * x))   := by
  rw [Real.sin_sq, Real.cos_sq]
  ring
#print axioms solution
