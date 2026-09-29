-- Prove2me | solution 1 for WorkbookRestored.plus_2762
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:21.385602+00:00
-- url     : https://prove2.me/submissions/198408a1-07bb-43b8-9c98-b4b715dfeca3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2762.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x > 0, x - Real.log (1 + x) > 0   := by
  intro x hx
  have h₁ : 0 < 1 + x := by linarith
  have h₂ := log_lt_sub_one_of_pos h₁
  linarith [h₂ (by linarith)]
#print axioms solution
