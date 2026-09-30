-- Prove2me | solution 1 for lean_workbook_plus_71420
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:14.19848+00:00
-- url     : https://prove2.me/submissions/87cb4d34-3298-4925-94c7-83ce468ea45a

import Mathlib.Analysis.Complex.Basic

theorem solution (U : Set (ℝ → ℝ)) (hU : U = {f : ℝ → ℝ | ∀ x, f x = f (-x)}) :
    (∀ f g : ℝ → ℝ, f ∈ U ∧ g ∈ U → f + g ∈ U) ∧
    (∀ f : ℝ → ℝ, f ∈ U → ∀ c : ℝ, c • f ∈ U) := by
  subst U
  constructor
  · rintro f g ⟨hf, hg⟩
    change ∀ x, f x + g x = f (-x) + g (-x)
    intro x
    rw [hf x, hg x]
  · intro f hf c
    change ∀ x, c * f x = c * f (-x)
    intro x
    rw [hf x]

#print axioms solution
