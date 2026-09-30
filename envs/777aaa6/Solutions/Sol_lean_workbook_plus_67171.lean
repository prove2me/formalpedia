-- Prove2me | solution 1 for lean_workbook_plus_67171
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:28.437461+00:00
-- url     : https://prove2.me/submissions/ee0bc122-a288-4c09-99cb-ec44ee19836d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y : ℝ, (x + y) * (f x - f y) = f (x^2) - f (y^2)) ↔
      ∃ a b : ℝ, ∀ x : ℝ, f x = a * x + b := by
  constructor
  · intro h
    refine ⟨f 1 - f 0, f 0, ?_⟩
    intro x
    have hx0 := h x 0
    have hx1 := h x 1
    norm_num only [zero_pow, one_pow, add_zero] at hx0 hx1
    nlinarith
  · rintro ⟨a, b, h⟩ x y
    rw [h x, h y, h (x^2), h (y^2)]
    ring
