-- Prove2me | solution 1 for WorkbookRestored.plus_78333
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:44:49.945738+00:00
-- url     : https://prove2.me/submissions/ee01e228-4a78-4d51-845f-4cd6c5c4d158

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_78333.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (θ_n : ℝ) (h₁ : 0 < θ_n ∧ θ_n < π/2) : ∃! θ_n1 : ℝ, θ_n1 = (θ_n + π)/3 ∧ 0 < θ_n1 ∧ θ_n1 < π/2   := by
  refine ⟨(θ_n + π) / 3, ⟨rfl, ?_, ?_⟩, ?_⟩
  · linarith [Real.pi_pos]
  · linarith [h₁.2]
  · intro y hy
    exact hy.1
#print axioms solution
