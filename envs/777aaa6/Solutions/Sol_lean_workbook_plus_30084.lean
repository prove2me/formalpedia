-- Prove2me | solution 1 for lean_workbook_plus_30084
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:24:34.191558+00:00
-- url     : https://prove2.me/submissions/c5ff7f01-c495-4703-88f9-ea0b4b534121

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (f : ℝ → ℝ): (∀ x y :ℝ, y * f x = x * f y) ↔ ∃ k:ℝ, ∀ x:ℝ, f x = k * x := by
  constructor
  · intro h
    refine ⟨f 1, ?_⟩
    intro x
    simpa [mul_comm] using h x 1
  · rintro ⟨k, h⟩ x y
    simp only [h]
    ring
