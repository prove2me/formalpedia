-- Prove2me | solution 1 for lean_workbook_plus_72970
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:05.874684+00:00
-- url     : https://prove2.me/submissions/4024c1d8-87ef-43f3-915f-9799d1cb3916

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (f : ℤ → ℤ)
    (h₁ : ∀ x, f (x^2 + 2*x) = f x * (f x + 2))
    (h₂ : ∀ x, f (x^2 + 2*x) = f (-x) * (f (-x) - 2)) :
    ∀ x, f (-x) = - f x := by
  intro x
  have hx := (h₁ x).symm.trans (h₂ x)
  have hneg := (h₁ (-x)).symm.trans (h₂ (-x))
  simp only [neg_neg] at hneg
  nlinarith

#print axioms solution
