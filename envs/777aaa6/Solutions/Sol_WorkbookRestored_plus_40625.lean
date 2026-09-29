-- Prove2me | solution 1 for WorkbookRestored.plus_40625
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:59.923275+00:00
-- url     : https://prove2.me/submissions/5bdfb3e2-0d38-4d64-a866-2dfca874d7cb

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_40625.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) (α : ℝ) (h₁ : a = Real.cos α) (h₂ : b = Real.sin α / Real.sqrt 3) : a^2 + 3 * b^2 = 1   := by
  rw [h₁,h₂,div_pow,sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  nlinarith [cos_sq_add_sin_sq α]
#print axioms solution
