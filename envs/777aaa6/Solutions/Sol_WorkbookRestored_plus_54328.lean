-- Prove2me | solution 1 for WorkbookRestored.plus_54328
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:53.230986+00:00
-- url     : https://prove2.me/submissions/10ba8a8c-1f3d-4e21-91be-1ed778eb803d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_54328.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (h : x ≥ y) : exp x - exp y ≥ 0   := by
  simpa only [sub_nonneg] using exp_le_exp.2 h
#print axioms solution
