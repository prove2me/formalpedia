-- Prove2me | solution 1 for WorkbookRestored.plus_41954
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:05.352467+00:00
-- url     : https://prove2.me/submissions/b33fd7a5-71cf-467e-8eb8-664a0bffbb1a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_41954.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B C a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (hA: 0 < A ∧ A <= π ∧ cos A = (b^2 + c^2 - a^2)/(2*b*c))  (hB: 0 < B ∧ B <= π ∧ cos B = (a^2 + c^2 - b^2)/(2*a*c)) (hC: 0 < C ∧ C <= π ∧ cos C = (a^2 + b^2 - c^2)/(2*a*b)) : (cos A * cos B)/(a * b) + (cos B * cos C)/(b * c) + (cos A * cos C)/(a * c) = (sin A)^2/(a^2)   := by
  have hs : sin A^2 = 1-cos A^2 := by nlinarith [sin_sq_add_cos_sq A]
  rw [hs,hA.2.2,hB.2.2,hC.2.2]
  field_simp [ha.ne',hb.ne',hc.ne']
  ring
#print axioms solution
