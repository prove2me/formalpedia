-- Prove2me | solution 1 for WorkbookRestored.plus_37377
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:55.414837+00:00
-- url     : https://prove2.me/submissions/c5ca1ae8-eee8-44ce-a631-5f73515cd366

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_37377.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ y : ℝ, (exp y + exp (-y)) ^ 2 ≥ (exp y - exp (-y)) ^ 2   := by
  exact fun y ↦ by nlinarith [exp_pos y, exp_pos (-y)]
#print axioms solution
