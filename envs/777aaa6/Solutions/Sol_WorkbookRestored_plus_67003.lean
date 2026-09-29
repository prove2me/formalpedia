-- Prove2me | solution 1 for WorkbookRestored.plus_67003
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:09.535815+00:00
-- url     : https://prove2.me/submissions/36c24efb-2bb3-4a9a-b586-456b3079eeb3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_67003.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) : 0 ≤ Real.sqrt (1 + (π - x) ^ 2) - Real.sqrt (1 + x ^ 2)   := by
  apply sub_nonneg.mpr
  apply Real.sqrt_le_sqrt
  nlinarith [hx.1, hx.2]
#print axioms solution
