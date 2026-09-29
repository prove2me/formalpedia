-- Prove2me | solution 1 for WorkbookRestored.plus_46535
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:11.728128+00:00
-- url     : https://prove2.me/submissions/6d7bbed2-463c-4b9b-a15b-d35accd102b5

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_46535.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x ∧ x < π) : (9 * (x ^ 2 * (sin x) ^ 2) + 4) / (x * sin x) ≥ 12   := by
  have h₁ : 0 < x*sin x := mul_pos hx.1 (sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  change 12 ≤ (9*(x^2*sin x^2)+4)/(x*sin x)
  rw [le_div_iff₀ h₁]
  nlinarith [sq_nonneg (3*x*sin x-2)]
#print axioms solution
