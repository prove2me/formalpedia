-- Prove2me | solution 1 for lean_workbook_plus_63979
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:07:49.963008+00:00
-- url     : https://prove2.me/submissions/ce0d7981-b5b3-4f18-b376-4bc6a5e6a13c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y : ℝ, f (x+y) = x+f y) ↔ ∃ a : ℝ, ∀ x : ℝ, f x = x+a := by
  constructor
  · intro h
    refine ⟨f 0, ?_⟩
    intro x
    simpa only [add_zero] using h x 0
  · rintro ⟨a, h⟩ x y
    rw [h (x+y), h y]
    ring
