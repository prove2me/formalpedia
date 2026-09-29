-- Prove2me | solution 1 for WorkbookRestored.plus_48665
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:14.394812+00:00
-- url     : https://prove2.me/submissions/e51d618b-cc3f-432d-88a1-446c1ab102a6

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_48665.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x z : ℝ) : Real.logb 2 x = z → Real.logb x 2 = 1 / z   := by
  exact fun h ↦ by rw [← h]; simp [Real.logb]
#print axioms solution
