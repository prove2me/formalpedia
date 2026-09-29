-- Prove2me | solution 1 for WorkbookRestored.plus_8810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:34:57.863076+00:00
-- url     : https://prove2.me/submissions/5f310b5e-d622-4a9d-a926-5ba130ea36a9

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_8810.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) :
  Real.sqrt (x * Real.cos x) ≤ (x + Real.cos x) / 2   := by
  have h₁ : 0 ≤ cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h₂ := sq_nonneg (x - cos x)
  rw [Real.sqrt_le_left] <;> nlinarith
#print axioms solution
