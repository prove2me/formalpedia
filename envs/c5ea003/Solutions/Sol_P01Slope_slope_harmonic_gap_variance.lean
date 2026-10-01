-- Prove2me | solution 1 for P01Slope.slope_harmonic_gap_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T22:05:13.638989+00:00
-- url     : https://prove2.me/submissions/e8a3c194-edaf-495d-86f8-d6e32f7e21d0

import Mathlib

open Matrix

theorem solution (p0 p1 q0 q1 : ℝ) :
    2 * q0 * (p0 + q0) * (p0 * p0 - p1 * p1) +
        2 * p0 * (p0 + q0) * (q0 * q0 - q1 * q1) -
        2 * p0 * q0 * ((p0 + q0) * (p0 + q0) - (p1 + q1) * (p1 + q1))
      = -2 * (p1 * q0 - q1 * p0) ^ 2 := by
  ring
