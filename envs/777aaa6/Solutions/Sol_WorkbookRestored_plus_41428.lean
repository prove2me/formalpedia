-- Prove2me | solution 1 for WorkbookRestored.plus_41428
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:03.215696+00:00
-- url     : https://prove2.me/submissions/f71c1dc2-6d5b-45ac-99a7-954e009923cc

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_41428.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  Real.log (1 + n * x / (n + 1)) ≤ Real.log (1 + n / (n + 1))   := by
  rcases hx with ⟨hx_left, hx_right⟩
  gcongr
  exact mul_le_of_le_one_right (Nat.cast_nonneg n) hx_right
#print axioms solution
