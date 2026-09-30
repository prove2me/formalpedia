-- Prove2me | solution 1 for lean_workbook_plus_45482
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:43.870045+00:00
-- url     : https://prove2.me/submissions/d54af864-006f-48b2-ab46-b5086ad18fab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem positive_rational_fixed_point (a : ℚ) (ha : 0 < a) :
    a = (7 + 1 / a) / (65 - 1 / a) ↔ a = 1 / 5 := by
  constructor
  · intro h
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hd : 65 - 1 / a ≠ 0 := by
      intro hz
      rw [hz, div_zero] at h
      linarith
    have he := (eq_div_iff hd).mp h
    field_simp at he
    have hf : (5 * a - 1) * (13 * a + 1) = 0 := by nlinarith
    have hn : 13 * a + 1 ≠ 0 := by linarith
    have hz := (mul_eq_zero.mp hf).resolve_right hn
    linarith
  · rintro rfl
    norm_num

theorem solution (m n : ℤ) (a : ℚ) (h₀ : 0 < a) (h₁ : 0 < n)
    (h₂ : ¬ 5 * m = 13 * n) (h₃ : (m : ℚ) / n = a)
    (h₄ : a = (7 + 1 / a) / (65 - 1 / a)) : a = 1 / 5 := by
  exact (positive_rational_fixed_point a h₀).mp h₄

#print axioms solution
