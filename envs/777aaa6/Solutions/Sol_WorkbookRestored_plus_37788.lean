-- Prove2me | solution 1 for WorkbookRestored.plus_37788
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:56.250843+00:00
-- url     : https://prove2.me/submissions/2fb35c9e-adea-4151-80b8-deab694d25c6

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_37788.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution {A B C : ℝ} (hA : 0 < A ∧ A ≤ π ∧ B ≤ π ∧ C ≤ π) (hB : 0 < B ∧ B ≤ π ∧ A ≤ π ∧ C ≤ π) (hC : 0 < C ∧ C ≤ π ∧ A ≤ π ∧ B ≤ π) : 9 / 4 + Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 ≥ Real.cos A + Real.cos B + Real.cos C   := by
  nlinarith [cos_le_one A, cos_le_one B, cos_le_one C, hA.1, hB.1, hC.1, hA.2.1, hB.2.1, hC.2.1, hA.2.2.1, hB.2.2.1, hC.2.2.1, hA.2.2.2, hB.2.2.2, hC.2.2.2]
#print axioms solution
