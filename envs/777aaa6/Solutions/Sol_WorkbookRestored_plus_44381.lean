-- Prove2me | solution 1 for WorkbookRestored.plus_44381
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:08.912245+00:00
-- url     : https://prove2.me/submissions/e3dd5e87-5df0-4260-98de-5e84a7e5be43

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_44381.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : x = 2^Real.logb 6 18 * 3^Real.logb 6 3) : x = 6   := by
  have h6 : log (6:ℝ) = log 2 + log 3 := by rw [show (6:ℝ)=2*3 by norm_num,log_mul (by norm_num) (by norm_num)]
  have h18 : log (18:ℝ) = log 2 + 2*log 3 := by
    rw [show (18:ℝ)=2*3^2 by norm_num,log_mul (by norm_num) (by norm_num),log_pow]
    ring
  have hcalc : log 2 * logb 6 18 + log 3 * logb 6 3 = log 6 := by
    unfold logb
    field_simp [ne_of_gt (log_pos (by norm_num : (1:ℝ)<6))]
    rw [h18,h6]
    ring
  rw [hx,rpow_def_of_pos (by norm_num : (0:ℝ)<2),rpow_def_of_pos (by norm_num : (0:ℝ)<3),←exp_add,hcalc,exp_log (by norm_num)]
#print axioms solution
