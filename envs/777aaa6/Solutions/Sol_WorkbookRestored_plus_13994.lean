-- Prove2me | solution 1 for WorkbookRestored.plus_13994
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:47.844204+00:00
-- url     : https://prove2.me/submissions/8776061a-7263-43d3-8223-f90fa48e8cff

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_13994. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (f : ℝ → ℝ) (h : f = fun t ↦ 4^t + 9^t) : ∀ t₁ t₂, t₁ < t₂ → f t₁ < f t₂   := by
  intro t₁ t₂ ht
  subst f
  exact add_lt_add (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ht) (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ht)
#print axioms solution
