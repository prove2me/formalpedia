-- Prove2me | solution 1 for lean_workbook_plus_47115
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:46:50.547258+00:00
-- url     : https://prove2.me/submissions/c3b4a958-21e7-48eb-aec3-545b61f31925

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y : ℚ) (k : ℝ) (h₁ : x + k * y = 0)
    (h₂ : ¬ k ∈ Set.range ((↑) : ℚ → ℝ)) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst y
    simp only [Rat.cast_zero, mul_zero, add_zero] at h₁
    constructor
    · exact_mod_cast h₁
    · rfl
  · exfalso
    apply h₂
    refine ⟨-x / y, ?_⟩
    push_cast
    have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    apply (div_eq_iff hyR).2
    linarith

#print axioms solution
