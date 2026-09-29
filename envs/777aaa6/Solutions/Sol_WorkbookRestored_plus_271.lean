-- Prove2me | solution 1 for WorkbookRestored.plus_271
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:35.591985+00:00
-- url     : https://prove2.me/submissions/01e052b6-9556-4bbb-a16a-765e29438201

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_271.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) : (1 - 8 * Real.sin x * Real.sin y * Real.cos (x + y)) = (2 * Real.cos (x + y) - Real.cos (x - y)) ^ 2 + Real.sin (x - y) ^ 2   := by
  simp [sub_sq, cos_add, cos_sub, sin_add, sin_sub]
  nlinarith [sin_sq_add_cos_sq x, sin_sq_add_cos_sq y]
#print axioms solution
