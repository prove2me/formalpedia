-- Prove2me | solution 1 for lean_workbook_plus_11576
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:52:50.660152+00:00
-- url     : https://prove2.me/submissions/e2cf9132-8735-47eb-b3dd-30fa0e40ce8a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y, (x + y) * (f x - f y) = (x - y) * (f x + f y)) ↔
    ∃ a : ℝ, ∀ x, f x = a * x := by
  constructor
  · intro h
    refine ⟨f 1, ?_⟩
    intro x
    nlinarith only [h x 1]
  · rintro ⟨a, h⟩ x y
    simp only [h]
    ring
