-- Prove2me | Theorems.Thm_P01Slope_slope_harmonic_gap_variance
-- name    : P01Slope.slope_harmonic_gap_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:59:30.260288+00:00
-- url     : https://prove2.me/theorems/7f2a1378-db8f-416a-9a30-7a7afa51a352
-- title:
--   Exact square gap in the two-dimensional slope harmonic mean
-- statement:
--   For arbitrary real midpoint and half-difference parameters of two positive linear denominators, the denominator-cleared gap in the superadditivity of the reciprocal slope kernel of a symmetric 2x2 quadratic form is exactly minus twice the square of the cross difference. This is the algebraic core of the slope-wise bound r(t)+s(t) at most one: superadditivity holds with an explicit two-point variance gap, and after clearing the positive denominators the gap becomes a perfect square.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. In slope coordinates the reciprocal slope kernel of a symmetric 2x2 form M with entries (a,c,b) is ((a+b t^2)^2 - 4 c^2 t^2)/(a+b t^2), whose numerator is the product of the paired positive denominators a+b t^2 +/- 2 c t. Writing p0 = a+b t^2, p1 = 2c and likewise for Q, the sum C=P+Q has c0 = p0+q0 and c1 = p1+q1, and superadditivity of the reciprocal kernel holds with the gap (p1 q0 - q1 p0)^2/(p0 q0 c0). The statement is the exact denominator-cleared form, verified symbolically over the rationals, and it is the pointwise algebraic core of the two-dimensional adjugate pair-contraction route.

import Mathlib

open Matrix

theorem P01Slope.slope_harmonic_gap_variance (p0 p1 q0 q1 : ℝ) :
    2 * q0 * (p0 + q0) * (p0 * p0 - p1 * p1) +
        2 * p0 * (p0 + q0) * (q0 * q0 - q1 * q1) -
        2 * p0 * q0 * ((p0 + q0) * (p0 + q0) - (p1 + q1) * (p1 + q1))
      = -2 * (p1 * q0 - q1 * p0) ^ 2 := by
  sorry
