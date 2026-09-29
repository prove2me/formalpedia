-- Prove2me | solution 1 for WorkbookRestored.plus_18380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:29.937348+00:00
-- url     : https://prove2.me/submissions/04a703c7-6137-4f4f-bac7-bea8fe6282f4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_18380.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) (x : ℝ) (h : a^2 + b^2 = 1) :
  a * Real.sin x + b * Real.cos x ≤ 1   := by
  have h2 : 0 ≤ (a * cos x - b * sin x) ^ 2 := sq_nonneg _
  nlinarith [Real.sin_sq_add_cos_sq x]
#print axioms solution
