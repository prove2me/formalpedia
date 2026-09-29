-- Prove2me | solution 1 for WorkbookRestored.plus_82892
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:39.013384+00:00
-- url     : https://prove2.me/submissions/6ef61de7-1b1e-47b1-a505-70eb5c3ac745

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_82892.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.logb 2 3 > Real.logb 3 2   := by
  rw [logb, logb]
  change log 2 / log 3 < log 3 / log 2
  have h2 : (0:ℝ)<log 2 := log_pos (by norm_num)
  have h3 : (0:ℝ)<log 3 := log_pos (by norm_num)
  have h23 : log 2 < log 3 := log_lt_log (by norm_num) (by norm_num)
  rw [div_lt_div_iff₀ h3 h2]
  nlinarith
#print axioms solution
