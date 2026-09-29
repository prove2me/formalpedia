-- Prove2me | solution 1 for WorkbookRestored.plus_37352
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:54.682299+00:00
-- url     : https://prove2.me/submissions/0846ffae-34b7-4828-9af1-2554127c988b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_37352.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ≠ 0 ∧ |x| < δ → |x * sin (1/x)| < ε   := by
  intro ε ε_pos
  refine' ⟨ε / 2, by linarith [ε_pos], fun x hx => _⟩
  have h₁ : |x| < ε / 2 := hx.2
  have h₂ : |sin (1 / x)| ≤ 1 := abs_sin_le_one _
  rw [abs_mul]
  nlinarith [abs_pos.mpr hx.1, hx.2, h₁]
#print axioms solution
