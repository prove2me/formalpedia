-- Prove2me | solution 1 for WorkbookRestored.plus_56140
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:56.35518+00:00
-- url     : https://prove2.me/submissions/805260aa-925e-4f03-b2bd-17fbad2628e6

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_56140.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α θ : ℝ) : (1 + Real.cos θ) * (1 + Real.cos α) = 4 * (Real.cos (θ / 2))^2 * (Real.cos (α / 2))^2   := by
  have hθ := cos_two_mul (θ/2)
  have hα := cos_two_mul (α/2)
  rw [show 2*(θ/2)=θ by ring] at hθ
  rw [show 2*(α/2)=α by ring] at hα
  rw [hθ,hα]
  ring
#print axioms solution
