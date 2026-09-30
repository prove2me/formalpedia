-- Prove2me | solution 1 for RybinAI2026.P01.artanh_upper_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:08:53.333512+00:00
-- url     : https://prove2.me/submissions/1bf8b9e9-29fa-4b8c-8113-6a3d9e590770

import Mathlib

theorem solution (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Real.artanh x ≤ x / Real.sqrt (1 - x ^ 2) := by
  have hmem : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith
  have hxA : 0 ≤ Real.artanh x := Real.artanh_nonneg hx
  have hys : Real.artanh x ≤ Real.sinh (Real.artanh x) :=
    (Real.self_le_sinh_iff).2 hxA
  rw [Real.sinh_artanh hmem] at hys
  exact hys
