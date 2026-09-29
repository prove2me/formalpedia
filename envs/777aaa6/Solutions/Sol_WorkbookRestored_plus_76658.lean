-- Prove2me | solution 1 for WorkbookRestored.plus_76658
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:27.747981+00:00
-- url     : https://prove2.me/submissions/948a48a2-52bc-4866-a140-37db81505f6f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_76658.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ u : ℝ, 0 < u ∧ u < 1 → (1 - u) ^ (1 / u) < exp (-1)   := by
  rintro u ⟨hu₁,hu₂⟩
  rw [rpow_def_of_pos (sub_pos.mpr hu₂),exp_lt_exp]
  rw [mul_one_div,div_lt_iff₀ hu₁]
  have h := log_lt_sub_one_of_pos (sub_pos.mpr hu₂) (by linarith : 1-u ≠ 1)
  linarith
#print axioms solution
