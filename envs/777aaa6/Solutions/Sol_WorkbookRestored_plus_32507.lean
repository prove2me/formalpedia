-- Prove2me | solution 1 for WorkbookRestored.plus_32507
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:39.758193+00:00
-- url     : https://prove2.me/submissions/c0c593c6-46d1-4313-8e71-f7d652db3979

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_32507.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B C : ℝ) (hA : A = π - (B + C)) (hB : 0 < B ∧ 0 < C) (hC : 0 < A ∧ 0 < B ∧ 0 < C) : sin B ^ 2 + sin C ^ 2 = 1 + cos A * cos B * cos C + cos A * sin B * sin C   := by
  simp [hA, hB, hC, sin_add, cos_add, sin_pi_sub]
  nlinarith [sin_sq_add_cos_sq B, sin_sq_add_cos_sq C]
#print axioms solution
