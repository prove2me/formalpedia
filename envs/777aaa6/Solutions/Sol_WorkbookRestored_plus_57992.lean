-- Prove2me | solution 1 for WorkbookRestored.plus_57992
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:01.038993+00:00
-- url     : https://prove2.me/submissions/6cefafd9-781a-4d9f-8a20-5c9e7c2d3b22

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_57992.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
  (1 - p ^ n) < exp (-p ^ n)   := by
  rcases eq_or_lt_of_le hp1 with (rfl | hp1)
  simp [hp0]
  exacts [Real.exp_pos _, one_sub_lt_exp_neg (by positivity)]
#print axioms solution
