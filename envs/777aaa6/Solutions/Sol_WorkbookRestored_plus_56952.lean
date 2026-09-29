-- Prove2me | solution 1 for WorkbookRestored.plus_56952
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:58.772984+00:00
-- url     : https://prove2.me/submissions/a66208dd-442e-4928-b205-509c7bf6cc7e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_56952.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 1 ≤ x) : Real.logb 2 x * Real.logb 2 (x + 1) + 1 ≥ 1 ∧ 1 > 0   := by
  refine' ⟨_, _⟩
  exacts [by nlinarith [logb_nonneg one_lt_two hx, logb_nonneg one_lt_two (by linarith : 1 ≤ x + 1)], by norm_num]
#print axioms solution
