-- Prove2me | solution 1 for WorkbookRestored.plus_45623
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:11.04332+00:00
-- url     : https://prove2.me/submissions/018a8af4-8686-4606-9489-94be681ba741

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_45623.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : 0 ≤ x ∧ x ≤ n) :
  (1 - x / n)^n ≤ exp (- x)   := by
  obtain ⟨h1, h2⟩ := hx
  simp [h1, h2, one_sub_div_pow_le_exp_neg]
#print axioms solution
