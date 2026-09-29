-- Prove2me | solution 1 for WorkbookRestored.plus_32152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:37.462767+00:00
-- url     : https://prove2.me/submissions/ecc57a8f-43fd-40d5-98a7-021597b960d5

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_32152.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ 2 * Real.sin x * Real.cos x ∧ 2 * Real.sin x * Real.cos x ≤ 1   := by
  simp [Set.mem_Ioo]
  intro x hx h'x
  rw [← sin_two_mul]
  exact ⟨sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith), sin_le_one (2 * x)⟩
#print axioms solution
