-- Prove2me | solution 1 for WorkbookRestored.plus_4758
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:04.500063+00:00
-- url     : https://prove2.me/submissions/9745e8a5-756d-46a2-8ced-5b89eb71915f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_4758.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, 1 ≤ x → 2 / (x * (1 + exp (-x))) ≥ 1 / x   := by
  intro x hx
  rw [ge_iff_le]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [exp_le_one_iff.2 (by linarith : -x ≤ 0)]
#print axioms solution
