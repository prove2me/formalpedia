-- Prove2me | solution 1 for lean_workbook_plus_10372
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:48:04.483611+00:00
-- url     : https://prove2.me/submissions/57daf2fe-17d1-48c1-9ec7-92d51a57a06a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (f : ℝ → ℝ) (hf : Continuous f)
    (h : ∀ x, 6 * f (f x) = 2 * f x + x) : Function.Injective f := by
  intro x y hxy
  have hx := h x
  have hy := h y
  rw [hxy] at hx
  linarith

#print axioms solution
