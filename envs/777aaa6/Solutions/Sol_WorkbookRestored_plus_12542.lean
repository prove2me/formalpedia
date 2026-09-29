-- Prove2me | solution 1 for WorkbookRestored.plus_12542
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:09.407281+00:00
-- url     : https://prove2.me/submissions/8a19cd6f-03f2-471f-82d7-5f6f5778e1d3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_12542.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (r₁ r₂ : ℝ) (θ : ℝ) : (1 - Real.cos θ) * (r₁ - r₂) ^ 2 ≥ 0   := by
  exact mul_nonneg (sub_nonneg.mpr (cos_le_one θ)) (sq_nonneg (r₁ - r₂))
#print axioms solution
