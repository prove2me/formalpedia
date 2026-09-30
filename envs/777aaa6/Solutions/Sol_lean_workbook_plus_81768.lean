-- Prove2me | solution 1 for lean_workbook_plus_81768
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:37.064203+00:00
-- url     : https://prove2.me/submissions/e49cf555-50c4-495e-afd4-78f9735f02fc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (ω : ℂ) (h₀ : ω ^ 3 = 1) (h₁ : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  have hp : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h₀
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h₁)

#print axioms solution
