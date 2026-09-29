-- Prove2me | solution 1 for WorkbookRestored.plus_71756
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:21.232991+00:00
-- url     : https://prove2.me/submissions/600295f9-6466-4a55-b17c-4984bf36c538

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_71756.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Real.logb 10 (12 * n) > Real.logb 10 75) :
  n > 6   := by
  contrapose! h₁
  interval_cases n <;> norm_num [h₀, h₁]
#print axioms solution
