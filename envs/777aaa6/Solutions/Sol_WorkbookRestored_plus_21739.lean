-- Prove2me | solution 1 for WorkbookRestored.plus_21739
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:41.82483+00:00
-- url     : https://prove2.me/submissions/37b0a436-e483-4d29-8fdf-e172812b0e31

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_21739.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, ContinuousAt (fun x => exp x) x   := by
  exact fun x ↦ continuous_exp.continuousAt
#print axioms solution
