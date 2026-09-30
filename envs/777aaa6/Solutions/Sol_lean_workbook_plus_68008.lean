-- Prove2me | solution 1 for lean_workbook_plus_68008
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:18.908345+00:00
-- url     : https://prove2.me/submissions/8a0415f4-0ca7-42ba-ba9a-5040c8074f7d

import Mathlib

theorem solution (f : ℝ → ℝ)
    (h : ∀ x y, (x + y) - f (x + y) = x - f x) :
    ∃ a, ∀ x, f x = x + a := by
  refine ⟨f 0, ?_⟩
  intro x
  have hx := h 0 x
  simp only [zero_add, zero_sub] at hx
  linarith
