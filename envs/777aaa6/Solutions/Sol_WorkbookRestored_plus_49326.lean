-- Prove2me | solution 1 for WorkbookRestored.plus_49326
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:43.497914+00:00
-- url     : https://prove2.me/submissions/c7c59add-9cc3-449b-8c35-8479bc9d4d54

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_49326.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 < Real.tan θ   := by
  exact fun θ hθ ↦ Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
#print axioms solution
