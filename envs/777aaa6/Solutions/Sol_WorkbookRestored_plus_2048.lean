-- Prove2me | solution 1 for WorkbookRestored.plus_2048
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:47.055819+00:00
-- url     : https://prove2.me/submissions/37dd8e4f-81be-4274-9682-f45a78205b34

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2048.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : (2:ℝ)^(Real.logb 2 5 - 2) = (2:ℝ)^(Real.logb 2 5) / (2:ℝ)^2   := by
  rw [Real.rpow_sub two_pos, Real.rpow_two]
#print axioms solution
