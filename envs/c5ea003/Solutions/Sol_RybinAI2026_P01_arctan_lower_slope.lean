-- Prove2me | solution 1 for RybinAI2026.P01.arctan_lower_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:08:37.155027+00:00
-- url     : https://prove2.me/submissions/9e6e8510-a4c3-4172-9b8c-59149cd4c76a

import Mathlib

theorem solution (x : ℝ) (hx : 0 ≤ x) :
    x / Real.sqrt (1 + x ^ 2) ≤ Real.arctan x := by
  rw [← Real.sin_arctan x]
  exact Real.sin_le (Real.arctan_nonneg.mpr hx)
