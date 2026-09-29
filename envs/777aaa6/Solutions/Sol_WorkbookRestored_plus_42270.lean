-- Prove2me | solution 1 for WorkbookRestored.plus_42270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:06.001912+00:00
-- url     : https://prove2.me/submissions/8469db9f-8fb2-4ce4-92b1-5350c48c2915

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_42270.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2:ℝ) ^ (2 * a) * a ^ a * b ^ b < (a + b) ^ (a + b) ↔ 2 * a * Real.log 2 + a * Real.log a + b * Real.log b - (a + b) * Real.log (a + b) < 0   := by
  rw [← log_lt_log_iff (by positivity) (by positivity)]
  rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity)]
  rw [log_rpow (by norm_num : (0:ℝ)<2),log_rpow ha,log_rpow hb,log_rpow (add_pos ha hb)]
  constructor <;> intro h <;> linarith
#print axioms solution
