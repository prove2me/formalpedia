-- Prove2me | solution 1 for lean_workbook_plus_66413
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:27.476449+00:00
-- url     : https://prove2.me/submissions/fdcf2e13-2a3e-4d39-a5bd-56cd044c0560

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem bound_and_equality (a b c : ℝ)
    (h : a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1)
    (h2 : a*b+b*c+c*a = 1) :
    a+b+c+a*b*c ≤ 2 ∧ (a+b+c+a*b*c = 2 ↔ a=1 ∨ b=1 ∨ c=1) := by
  have hid : (1-a)*(1-b)*(1-c) = 2-(a+b+c+a*b*c) := by
    nlinarith only [h2]
  have hp := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr h.1.2) (sub_nonneg.mpr h.2.1.2))
    (sub_nonneg.mpr h.2.2.2)
  constructor
  · linarith only [hid, hp]
  · constructor
    · intro heq
      have hz : (1-a)*(1-b)*(1-c) = 0 := by linarith only [hid, heq]
      rcases mul_eq_zero.mp hz with hab | hc
      · rcases mul_eq_zero.mp hab with ha | hb
        · exact Or.inl (sub_eq_zero.mp ha).symm
        · exact Or.inr (Or.inl (sub_eq_zero.mp hb).symm)
      · exact Or.inr (Or.inr (sub_eq_zero.mp hc).symm)
    · intro heq
      rcases heq with ha | hb | hc
      all_goals simp_all only [sub_self, zero_mul, mul_zero]
      all_goals linarith only [hid]

theorem solution (a b c : ℝ)
    (h : a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1)
    (h2 : a*b+b*c+c*a = 1) : a+b+c+a*b*c ≤ 2 := by
  exact (bound_and_equality a b c h h2).1
