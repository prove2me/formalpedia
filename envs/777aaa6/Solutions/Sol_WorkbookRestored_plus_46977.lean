-- Prove2me | solution 1 for WorkbookRestored.plus_46977
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:12.974582+00:00
-- url     : https://prove2.me/submissions/8286da04-24bb-437e-af82-05311e2cd081

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_46977.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (t : ℝ) (ht : t = sin x + cos x) : sin x * cos x = (t^2 - 1) / 2 ∧ |t| ≤ Real.sqrt 2   := by
  rw [ht]
  constructor
  · nlinarith [sin_sq_add_cos_sq x]
  · apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (sin x-cos x),sin_sq_add_cos_sq x]
#print axioms solution
