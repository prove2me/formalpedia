-- Prove2me | solution 1 for WorkbookRestored.plus_25157
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:47.252393+00:00
-- url     : https://prove2.me/submissions/c1791d1f-7d3e-42cb-9316-4d1fe5833331

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_25157.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : sin x = cos (π / 2 - x)   := by
  simp [sub_eq_add_neg, cos_add, cos_neg]
#print axioms solution
