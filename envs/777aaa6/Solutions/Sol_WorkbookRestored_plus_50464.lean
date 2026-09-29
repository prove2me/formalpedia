-- Prove2me | solution 1 for WorkbookRestored.plus_50464
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:45.537625+00:00
-- url     : https://prove2.me/submissions/ae4542c8-6080-47df-af18-132b9523c6a0

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_50464.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 1 < Real.log 3 / Real.log 2 ∧ Real.log 3 / Real.log 2 < 2   := by
  have h2 : 0 < log (2:ℝ) := log_pos (by norm_num)
  constructor
  · rw [lt_div_iff₀ h2]
    simpa using log_lt_log (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)<3)
  · rw [div_lt_iff₀ h2]
    have h := log_lt_log (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)<4)
    rw [show (4:ℝ)=2^2 by norm_num,log_pow] at h
    simpa using h
#print axioms solution
