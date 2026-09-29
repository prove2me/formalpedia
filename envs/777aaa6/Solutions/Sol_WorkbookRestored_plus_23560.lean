-- Prove2me | solution 1 for WorkbookRestored.plus_23560
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:45.00257+00:00
-- url     : https://prove2.me/submissions/25734236-2930-4f72-9acf-c171d1d0ca4d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_23560.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) (A : ℝ) : a^2 + (-2 * Real.cos A) * a + (Real.cos A)^2 - 3 * (Real.sin A)^2 ≤ 0 ↔ (a - Real.cos A + Real.sqrt 3 * Real.sin A) * (a - Real.cos A - Real.sqrt 3 * Real.sin A) ≤ 0   := by
  have h : a^2 + (-2 * cos A) * a + cos A^2 - 3 * sin A^2 =
      (a - cos A + sqrt 3 * sin A) * (a - cos A - sqrt 3 * sin A) := by
    nlinarith [sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  rw [h]
#print axioms solution
