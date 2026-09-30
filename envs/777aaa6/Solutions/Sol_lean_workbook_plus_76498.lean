-- Prove2me | solution 1 for lean_workbook_plus_76498
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:35:55.234177+00:00
-- url     : https://prove2.me/submissions/cc3b0dc3-101b-4574-8c44-c58162112288

import Mathlib

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 0 ∨ f 0 = 1 := by
  have hzero := hf 0 0
  simp only [zero_add] at hzero
  have hfactor : f 0 * (f 0 - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl h
  · right
    linarith
