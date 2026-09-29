-- Prove2me | solution 1 for WorkbookRestored.plus_51735
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:47.814069+00:00
-- url     : https://prove2.me/submissions/1e7482bd-4198-4547-9b47-5930572df606

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51735.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : (Real.sqrt 3 ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = Real.sqrt 9   := by
  rw [← Real.rpow_mul (Real.sqrt_nonneg _)]
  norm_num [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
#print axioms solution
