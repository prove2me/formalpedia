-- Prove2me | solution 1 for WorkbookRestored.plus_43176
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:06.798543+00:00
-- url     : https://prove2.me/submissions/e9e77e2b-3c4d-494b-855b-d9a87237680b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_43176.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ m : ℝ, m ∈ Set.Icc (-1) 1 → ∃ θ : ℝ, θ ∈ Set.Icc (-Real.pi/2) (Real.pi/2) ∧ m = Real.sin θ   := by
  refine' fun m hm => ⟨Real.arcsin m, ⟨by linarith [Real.neg_pi_div_two_le_arcsin m, Real.arcsin_le_pi_div_two m], by linarith [Real.neg_pi_div_two_le_arcsin m, Real.arcsin_le_pi_div_two m]⟩, by simp [Real.sin_arcsin hm.1 hm.2]⟩
#print axioms solution
