-- Prove2me | solution 1 for lean_workbook_plus_5481
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:55:58.966716+00:00
-- url     : https://prove2.me/submissions/8d8c6609-2715-4877-8836-63d4f7151939

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c x y : ℤ) (n m : ℤ) (h₁ : a > 0) (h₂ : n = a^2 + 1) (h₃ : m = a^2)
    (h₄ : (b, c) = (y, x)) : a^2 + b^2 + (a * b)^2 = c^2 ↔ x^2 - n * y^2 = m := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₄
  subst h₂ h₃
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h
