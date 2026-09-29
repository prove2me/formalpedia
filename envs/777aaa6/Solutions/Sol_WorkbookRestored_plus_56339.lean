-- Prove2me | solution 1 for WorkbookRestored.plus_56339
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:57.226371+00:00
-- url     : https://prove2.me/submissions/10d0cba6-2aa9-4e19-94b3-97b6a61740cf

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_56339.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : Real.logb a b = 1 / Real.logb b a   := by
  simp [logb, ha, hb]
#print axioms solution
