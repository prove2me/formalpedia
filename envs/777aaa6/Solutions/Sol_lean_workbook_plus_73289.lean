-- Prove2me | solution 1 for lean_workbook_plus_73289
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:57.105023+00:00
-- url     : https://prove2.me/submissions/b571de6c-ce3e-4e6a-ae2d-4cae6ca25def

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

theorem solution (f : ℝ → ℝ) (h₀ : f 1 = 1)
    (h₁ : ∀ x, f (x ^ 2) = (f x) ^ 2) : ∀ x ≥ 0, 0 ≤ f x := by
  intro x hx
  have hs := h₁ (Real.sqrt x)
  rw [Real.sq_sqrt hx] at hs
  rw [hs]
  exact sq_nonneg _

#print axioms solution
