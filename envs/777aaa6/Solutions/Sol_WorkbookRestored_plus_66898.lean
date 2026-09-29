-- Prove2me | solution 1 for WorkbookRestored.plus_66898
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:16.547857+00:00
-- url     : https://prove2.me/submissions/3f94df38-dfc7-46ae-98b3-0725005a9c8e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_66898.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  Real.logb 4 6 = Real.logb 2 (Real.sqrt 6)   := by
  rw [logb,logb,log_sqrt (by norm_num),show (4:ℝ)=2^2 by norm_num,log_pow]
  ring
#print axioms solution
