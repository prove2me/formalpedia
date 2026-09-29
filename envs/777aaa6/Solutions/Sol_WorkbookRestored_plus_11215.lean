-- Prove2me | solution 1 for WorkbookRestored.plus_11215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:01.657094+00:00
-- url     : https://prove2.me/submissions/667ddf53-790d-4db4-98b2-90d4e3d5c7c7

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_11215.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y z: ℝ) : 3 * (Real.cos x ^ 2 + Real.cos y ^ 2 + Real.cos z ^ 2) ≥ (Real.cos x + Real.cos y + Real.cos z) ^ 2   := by
  nlinarith [sq_nonneg (cos x - cos y), sq_nonneg (cos y - cos z), sq_nonneg (cos z - cos x)]
#print axioms solution
