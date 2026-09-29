-- Prove2me | solution 1 for WorkbookRestored.plus_18746
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:30.613573+00:00
-- url     : https://prove2.me/submissions/4eea73d5-5f5f-419b-8c15-bd24c6027e0a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_18746.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (u : ℝ) (hu : 0 < u) : u / (1 + exp (-u)) < u   := by
  rw [div_lt_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (exp_pos _).le)]
  nlinarith [exp_pos (-u), hu]
#print axioms solution
