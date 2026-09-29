-- Prove2me | solution 1 for WorkbookRestored.plus_41357
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:02.407985+00:00
-- url     : https://prove2.me/submissions/92447003-552a-426f-8f40-4359f99bf45e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_41357.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : tan x = sin x / cos x   := by
  rw [Real.tan_eq_sin_div_cos]
#print axioms solution
