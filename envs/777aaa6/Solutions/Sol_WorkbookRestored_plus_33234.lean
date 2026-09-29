-- Prove2me | solution 1 for WorkbookRestored.plus_33234
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:43.400553+00:00
-- url     : https://prove2.me/submissions/9cc8b48a-bbb6-4ac4-8cf1-b8e7c188e0af

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33234.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x : ℝ)
  (h₀ : Real.sin (x + Real.pi / 4) = 0) :
  ∃ k : ℤ, x = k * Real.pi - Real.pi / 4   := by
  obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 h₀
  exact ⟨k, by linarith [hk]⟩
#print axioms solution
