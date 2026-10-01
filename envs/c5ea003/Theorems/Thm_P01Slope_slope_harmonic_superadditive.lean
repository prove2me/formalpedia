-- Prove2me | Theorems.Thm_P01Slope_slope_harmonic_superadditive
-- name    : P01Slope.slope_harmonic_superadditive
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T22:03:40.635988+00:00
-- url     : https://prove2.me/theorems/3cb14ad7-db7f-4246-9033-b8c58896774c
-- title:
--   Superadditivity of the two-dimensional reciprocal slope kernel
-- statement:
--   Whenever both paired denominators of two symmetric 2x2 slope forms are positive, the reciprocal slope kernel is superadditive under addition of the forms. This is the pointwise statement that yields the slope-wise bound r(t) + s(t) at most one, which is the only slope-wise input the two-dimensional adjugate pair-contraction argument uses.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. The reciprocal slope kernel of a symmetric 2x2 form is the equal-weight harmonic mean of its paired positive denominators, and the harmonic mean is superadditive. The exact gap is published separately as P01Slope.slope_harmonic_gap_variance, where it is twice a square divided by the product of the three midpoints. The hypotheses are exactly the positivity conditions that the two-dimensional slope representation supplies for a positive-definite form at every slope.

import Mathlib

open Matrix

theorem P01Slope.slope_harmonic_superadditive (p0 p1 q0 q1 : ℝ)
    (hp0 : 0 < p0) (hq0 : 0 < q0) (hp1 : p1 ^ 2 < p0 ^ 2) (hq1 : q1 ^ 2 < q0 ^ 2) :
    (p0 ^ 2 - p1 ^ 2) / p0 + (q0 ^ 2 - q1 ^ 2) / q0 ≤
      ((p0 + q0) ^ 2 - (p1 + q1) ^ 2) / (p0 + q0) := by
  sorry
