-- Prove2me | solution 1 for WorkbookRestored.plus_30757
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:33.305006+00:00
-- url     : https://prove2.me/submissions/2804f9c7-b981-4ec5-a882-efd750e68ad7

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_30757.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : (Real.logb 2 9) * (Real.logb 3 7) * (Real.logb 7 8) = 6   := by
  rw [show (9 : ℝ) = 3^2 by norm_num, show (7 : ℝ) = 7^1 by norm_num, show (8 : ℝ) = 2^3 by norm_num]
  simp [Real.logb]
  norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
#print axioms solution
