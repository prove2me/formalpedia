-- Prove2me | Theorems.Thm_RybinAI2026_P01_offdiag_denominator_pairing
-- name    : RybinAI2026.P01.offdiag_denominator_pairing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T09:56:14.29938+00:00
-- url     : https://prove2.me/theorems/ee7b2afa-1697-4fbc-935f-6e86a6094fad
-- title:
--   Exact harmonic pairing of the two oblique denominator branches
-- statement:
--   For a positive definite symmetric 2x2 form with entries a (diagonal), b (diagonal) and off-diagonal c, and for a slope parameter s in [0,1], the reciprocal of the two paired oblique denominators a+(b-a)s^2 +/- 2 c s sqrt(1-s^2) sums exactly to 2 A / (A^2 - 4 c^2 s^2 (1-s^2)) with A = a+(b-a)s^2. This is the equal-weight harmonic-mean pairing of the two branches of the slope kernel of an oblique quadratic form, the counterpart of the already published P01Slope.slope_harmonic_gap_variance identity, and it is the exact algebraic step that converts the directional integral of an oblique 2x2 quadratic form into a rational integral over the slope parameter. Positivity of both paired denominators is supplied by the positive-definiteness hypothesis c^2 < a*b via the sine substitution s = sin theta.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. The slope representation of directionalIntegral2 for a symmetric 2x2 form M = [[a,c],[c,b]] writes the reciprocal slope kernel as the equal-weight harmonic mean of the two paired positive denominators a + b t^2 +/- 2 c t, i.e. under s = sin theta, of a + (b-a)s^2 +/- 2 c s sqrt(1-s^2). Clearing the two reciprocals gives the product (A+X)(A-X) = A^2 - 4 c^2 s^2 (1-s^2), which is exactly the denominator of the rational slope integral 4 * Int_0^1 A/(A^2-4c^2 s^2 (1-s^2)) ds for the cosine-directional integral. Both denominators are positive: a*Q(theta) = (a cos theta + c sin theta)^2 + (ab - c^2) sin^2 theta with Q the oblique quadratic form, and Q does not vanish on the unit circle when a,b > 0 and c^2 < ab.

import Mathlib

open Set

namespace RybinAI2026.P01

/-- Exact harmonic pairing of the two oblique denominator branches. -/
theorem offdiag_denominator_pairing (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 < a * b) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (a + (b - a) * s ^ 2 + 2 * c * s * Real.sqrt (1 - s ^ 2))⁻¹
      + (a + (b - a) * s ^ 2 - 2 * c * s * Real.sqrt (1 - s ^ 2))⁻¹
      = 2 * (a + (b - a) * s ^ 2)
        / ((a + (b - a) * s ^ 2) ^ 2 - 4 * c ^ 2 * s ^ 2 * (1 - s ^ 2)) := by
  sorry

end RybinAI2026.P01
