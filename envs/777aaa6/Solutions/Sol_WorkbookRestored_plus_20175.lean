-- Prove2me | solution 1 for WorkbookRestored.plus_20175
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:36.92141+00:00
-- url     : https://prove2.me/submissions/7fbb75fd-1e43-45e9-b907-9c30cf7178dd

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_20175.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (h₁ : 0 ≤ x ∧ x ≤ 1) (h₂ : y = arcsin x) : cos y = Real.sqrt (1 - x^2)   := by
  rw [h₂, Real.cos_arcsin]
#print axioms solution
