-- Prove2me | solution 1 for lean_workbook_plus_69811
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:12.131911+00:00
-- url     : https://prove2.me/submissions/94610f05-71a6-47e8-8f9a-7a414875e91d

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (2 * f x) = f (x - f y) + f x + y := by
  subst hf
  intro x y
  simp only
  ring
