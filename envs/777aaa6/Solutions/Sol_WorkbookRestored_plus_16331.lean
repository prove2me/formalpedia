-- Prove2me | solution 1 for WorkbookRestored.plus_16331
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:23.15887+00:00
-- url     : https://prove2.me/submissions/6b53db41-3b91-4443-b9cf-96e379d8ca4f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_16331.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (f : ℝ → ℝ) (g : ℝ → ℝ) (h₁ : ∀ x, f x = exp (g x)) (h₂ : ∀ x y, g (x + y) = g x + g y) : ∀ x y, f (x + y) = f x * f y   := by
  exact fun x y ↦ by rw [h₁, h₁, h₁, h₂, exp_add]
#print axioms solution
