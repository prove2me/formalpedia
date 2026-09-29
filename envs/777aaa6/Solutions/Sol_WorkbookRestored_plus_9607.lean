-- Prove2me | solution 1 for WorkbookRestored.plus_9607
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:00.914627+00:00
-- url     : https://prove2.me/submissions/01c72857-621a-4a12-bec6-5327b8b5d441

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_9607.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : sin x = 0 ↔ ∃ n : ℤ, x = n * π   := by
  simp [Real.sin_eq_zero_iff]
  constructor <;> rintro ⟨n, rfl⟩ <;> exact ⟨n, rfl⟩
#print axioms solution
