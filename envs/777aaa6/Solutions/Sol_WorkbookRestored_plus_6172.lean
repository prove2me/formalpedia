-- Prove2me | solution 1 for WorkbookRestored.plus_6172
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:10.604368+00:00
-- url     : https://prove2.me/submissions/ad21722b-701b-4d84-9bfb-8f6bc2353026

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_6172.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ a b c d : ℝ, a = 20 ∧ b = 40 → c = 30 ∧ d = 10 → sin a + sin b = 2 * sin c * cos d   := by
  rintro a b c d ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  rw [show (20 : ℝ) = 30 - 10 by norm_num, show (40 : ℝ) = 30 + 10 by norm_num]
  simp [sin_add, sin_sub, mul_comm, mul_assoc, mul_left_comm]
  ring
#print axioms solution
