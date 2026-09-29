-- Prove2me | solution 1 for WorkbookRestored.plus_56081
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:55.6393+00:00
-- url     : https://prove2.me/submissions/9d791ffe-dade-4fd2-a803-1d6b92c4dbb9

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_56081.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : (1 : ℝ) / ((2 - Real.cos x) * (3 - Real.cos x)) = 1 / (2 - Real.cos x) - 1 / (3 - Real.cos x)   := by
  rw [div_sub_div]
  field_simp <;> ring
  all_goals nlinarith [Real.cos_sq_add_sin_sq x]
#print axioms solution
