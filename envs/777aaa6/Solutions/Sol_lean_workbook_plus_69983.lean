-- Prove2me | solution 1 for lean_workbook_plus_69983
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:29.171916+00:00
-- url     : https://prove2.me/submissions/87f01f58-0f25-42f9-a9c6-44a7973c460f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y, f x * y + 1 = f (x * y) + y) ↔
      ∃ k : ℝ, ∀ x, f x = k * x + 1 := by
  constructor
  · intro h
    refine ⟨f 1 - 1, ?_⟩
    intro x
    have hx := h 1 x
    rw [one_mul] at hx
    nlinarith
  · rintro ⟨k, h⟩ x y
    rw [h x, h (x * y)]
    ring
