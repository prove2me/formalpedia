-- Prove2me | solution 1 for WorkbookRestored.plus_20955
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:39.020743+00:00
-- url     : https://prove2.me/submissions/e1bd0b42-59d2-4004-b86a-620293439b9e

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_20955.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (u : ℝ) (h : 0 < u) (h' : u < 1) : Real.log (1 - u) < -u   := by
  have h₁ : 0 < 1 - u := by linarith
  have h₂ := log_lt_sub_one_of_pos h₁
  linarith [h₁, h₂ (by linarith)]
#print axioms solution
