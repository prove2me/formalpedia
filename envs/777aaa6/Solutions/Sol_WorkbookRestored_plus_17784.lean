-- Prove2me | solution 1 for WorkbookRestored.plus_17784
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:28.476868+00:00
-- url     : https://prove2.me/submissions/dfc4f5e3-a0d6-478b-8208-7123910263b1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_17784.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (f : ℝ → ℝ) (f_def : ∀ x, f x = sin x / (1 + x ^ 4)) : ∀ x, f (-x) = -f x   := by
  simp [f_def, sin_neg, add_comm]
  exact fun x ↦ by ring
#print axioms solution
