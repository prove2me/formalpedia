-- Prove2me | solution 1 for lean_workbook_plus_33033
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:02:09.440312+00:00
-- url     : https://prove2.me/submissions/136c37ed-707d-4beb-b012-d784c1f3f174

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (h₁ : Monotone f)
    (h₂ : ∀ x, f (f x) = (f x) ^ 2) (h₃ : ∀ x, f (-f x) = (f x) ^ 2) :
    ∀ x ∈ Set.range f, f x = f (-x) := by
  rintro _ ⟨x, rfl⟩
  exact (h₂ x).trans (h₃ x).symm

#print axioms solution
