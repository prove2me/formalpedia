-- Prove2me | solution 1 for WorkbookRestored.plus_27783
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:59.762802+00:00
-- url     : https://prove2.me/submissions/f0520373-a830-4f56-b1a7-97dd8cd90fd2

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_27783.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, sin (7 * x) = 0 ↔ ∃ k : ℤ, x = k * π / 7   := by
  simp [Real.sin_eq_zero_iff]
  exact fun x ↦ ⟨fun h ↦ by rcases h with ⟨n, hn⟩; exact ⟨n, by linarith⟩, fun h ↦ by rcases h with ⟨k, hk⟩; exact ⟨k, by linarith⟩⟩
#print axioms solution
