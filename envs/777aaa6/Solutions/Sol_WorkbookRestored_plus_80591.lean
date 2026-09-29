-- Prove2me | solution 1 for WorkbookRestored.plus_80591
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:35.983774+00:00
-- url     : https://prove2.me/submissions/fd95ca74-d2a3-44fe-bcb1-009f4812203e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_80591.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : Real.log x = Real.log 6) :
  x = 6   := by
  rw [← Real.exp_log h₀, ← Real.exp_log (show (0 : ℝ) < 6 by norm_num), h₁]
#print axioms solution
