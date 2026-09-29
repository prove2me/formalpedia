-- Prove2me | solution 1 for WorkbookRestored.plus_19379
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:33.317661+00:00
-- url     : https://prove2.me/submissions/12f7e4c0-f608-49d6-b624-174114f8ae46

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_19379.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x: ℝ) (hx: 0 ≤ x ∧ x ≤ π/2) :
  1 ≤ 2 - Real.sin x + Real.cos x ∧ 2 - Real.sin x + Real.cos x ≤ 3   := by
  have h1 : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h2 : 0 ≤ sin x := sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  constructor <;> nlinarith [cos_sq_add_sin_sq x]
#print axioms solution
