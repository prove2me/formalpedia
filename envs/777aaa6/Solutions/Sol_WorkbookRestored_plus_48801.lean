-- Prove2me | solution 1 for WorkbookRestored.plus_48801
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:42.754213+00:00
-- url     : https://prove2.me/submissions/7470b228-45b2-4a94-b8c9-67ed61a4bd24

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_48801.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (n : ℝ)
  (h : ℝ)
  (h₀ : 0 < n)
  (h₁ : 0 < h)
  (h₂ : (0.9^h) * n = 0.5 * n) :
  h = Real.log 0.5 / Real.log 0.9   := by
  field_simp [Real.log_mul, h₀.ne', h₁.ne'] at h₂ ⊢
  norm_num at h₂ ⊢
  rw [← h₂, Real.log_rpow] <;> norm_num
#print axioms solution
