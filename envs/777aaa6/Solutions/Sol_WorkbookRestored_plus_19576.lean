-- Prove2me | solution 1 for WorkbookRestored.plus_19576
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:34.770018+00:00
-- url     : https://prove2.me/submissions/1e96662a-c99b-42c4-b627-0ef0da5e9ce1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_19576.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : tan x < 0) : (sin x ≠ 0 ∧ cos x ≠ 0 ∧ sin x * cos x < 0)   := by
  rw [tan_eq_sin_div_cos] at hx
  aesop
  have := div_neg_iff.mp hx
  rcases this with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> nlinarith [h₁, h₂]
#print axioms solution
