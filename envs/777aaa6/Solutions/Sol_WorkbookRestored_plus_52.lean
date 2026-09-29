-- Prove2me | solution 1 for WorkbookRestored.plus_52
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:32.277186+00:00
-- url     : https://prove2.me/submissions/d1ea08d0-94c1-48ff-9c64-913c8ec981e7

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_52.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, Real.cos (2 * x) ^ 2 = (1 + Real.cos (4 * x)) / 2   := by
  simp [cos_sq, sin_sq, sub_eq_add_neg, add_assoc]
  exact fun x ↦ by ring
#print axioms solution
