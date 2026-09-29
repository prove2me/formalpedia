-- Prove2me | solution 1 for WorkbookRestored.plus_70928
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:18.876271+00:00
-- url     : https://prove2.me/submissions/c8b54d10-f9a6-4b64-b23d-27a03cf75ba4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_70928.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x ≥ 0, exp (-x) ≤ 1   := by
  exact fun x hx ↦ by rw [Real.exp_le_one_iff]; linarith
#print axioms solution
