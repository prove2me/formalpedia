-- Prove2me | solution 1 for lean_workbook_plus_71668
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:05.942096+00:00
-- url     : https://prove2.me/submissions/992eb045-75b2-4e65-8a7a-0ced11d67ee5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f (f x) = f x + 8 * x) :
    Function.Injective f := by
  intro x y hxy
  have hff := congrArg f hxy
  rw [hf x, hf y] at hff
  linarith

#print axioms solution
