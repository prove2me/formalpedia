-- Prove2me | solution 1 for WorkbookRestored.plus_40
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:31.280922+00:00
-- url     : https://prove2.me/submissions/69112698-074a-4745-b919-871b36246c98

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_40.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  ∀ θ : ℝ, 0 < θ ∧ θ < Real.pi / 4 → Real.cos θ > Real.sin θ   := by
  intro θ h₁
  rw [← cos_pi_div_two_sub, ← sin_pi_div_two_sub]
  rw [Real.sin_pi_div_two_sub]
  exact cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
#print axioms solution
