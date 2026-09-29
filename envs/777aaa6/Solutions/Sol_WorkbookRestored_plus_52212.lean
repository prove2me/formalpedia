-- Prove2me | solution 1 for WorkbookRestored.plus_52212
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:47.451987+00:00
-- url     : https://prove2.me/submissions/6e461a46-4302-4030-9bf7-08bf27c5de0e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_52212.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) (h₁ : π < θ) (h₂ : θ < 3 * π / 2) : sin θ < 0 ∧ cos θ < 0   := by
  constructor
  · rw [← sin_pi_sub]
    exact sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  · exact cos_neg_of_pi_div_two_lt_of_lt (by linarith [pi_pos]) (by linarith)
#print axioms solution
