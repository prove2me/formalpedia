-- Prove2me | solution 1 for WorkbookRestored.plus_38285
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:56.973794+00:00
-- url     : https://prove2.me/submissions/bd752cdd-48d7-4d23-b388-ce407dfa1aee

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_38285.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : sin x + cos x = 0.8) : sin x ^ 3 + cos x ^ 3 = 0.944   := by
  ring_nf at hx ⊢
  have h1 : sin x ^ 3 + cos x ^ 3 = (sin x + cos x) * (sin x ^ 2 - sin x * cos x + cos x ^ 2) := by ring
  rw [h1, hx]
  nlinarith [Real.sin_sq_add_cos_sq x]
#print axioms solution
