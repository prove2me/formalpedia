-- Prove2me | solution 1 for WorkbookRestored.plus_19076
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:31.273297+00:00
-- url     : https://prove2.me/submissions/d468abe3-00a4-4f19-a32c-f592cf71824c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_19076.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) (ha : a = Real.exp 1) (hb : b = Real.log 2) : a^b = 2   := by
  simp [ha, hb, Real.exp_log]
#print axioms solution
