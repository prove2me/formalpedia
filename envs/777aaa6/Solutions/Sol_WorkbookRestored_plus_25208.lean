-- Prove2me | solution 1 for WorkbookRestored.plus_25208
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:47.964283+00:00
-- url     : https://prove2.me/submissions/cb389330-ddf7-4628-8276-5cfaf84ac31a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_25208.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ n : ℕ, 2 * Real.cos (π / 2 ^ (n + 1)) + 2 = 4 * (Real.cos (π / 2 ^ (n + 2))) ^ 2   := by
  exact fun n ↦ by rw [cos_sq, ← sub_eq_zero]; ring
#print axioms solution
