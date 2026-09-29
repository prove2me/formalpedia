-- Prove2me | solution 1 for WorkbookRestored.plus_66230
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:15.143017+00:00
-- url     : https://prove2.me/submissions/2c0d17ee-c3f8-473b-801c-22e42171e200

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_66230.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : (sin x + cos x)^2 = π^2 / 4^2) : sin x * cos x = (π^2 - 16) / 32   := by
  field_simp [sin_sq_add_cos_sq] at hx ⊢
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
