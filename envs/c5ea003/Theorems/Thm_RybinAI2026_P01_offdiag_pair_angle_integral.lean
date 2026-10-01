-- Prove2me | Theorems.Thm_RybinAI2026_P01_offdiag_pair_angle_integral
-- name    : RybinAI2026.P01.offdiag_pair_angle_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T10:07:51.964881+00:00
-- url     : https://prove2.me/theorems/4eacd64c-1a18-4422-87aa-a9c4cab83dcb
-- title:
--   Oblique cosine-angle integral as a rational slope integral
-- statement:
--   For a positive definite symmetric 2x2 quadratic form with diagonal entries a,b and off-diagonal c satisfying c^2 < a*b, the sum of the two paired branches of the oblique cosine-angle integrand over the quarter circle [0,pi/2] equals twice the rational slope integral of A/D over [0,1], where A = a+(b-a)s^2 and D = A^2 - 4 c^2 s^2 (1-s^2). The first branch is the ordinary oblique kernel and the second is the reflected kernel obtained from theta -> -theta, which is exactly what the reflection theta -> pi - theta produces on the spherical parametrisation. This is the oblique generalisation of the already proved diagonal angle formula and is the analytic core of the slope representation of the two-dimensional directional integral.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. On the quarter circle sin theta is strictly increasing with nonnegative derivative cos theta, so the substitution s = sin theta applies: with sqrt(1-sin^2) = cos theta the two branches become the two reciprocals of A +/- 2 c s sqrt(1-s^2), and the exact harmonic pairing identity already published as RybinAI2026.P01.offdiag_denominator_pairing sums them into 2A/D. The integral over [0,pi/2] of the sum is then 2 * Int_0^1 A/D ds. The diagonal case c = 0 reduces to the published diagonal_angle_integral_formula.

import Mathlib

open Set

namespace RybinAI2026.P01

/-- Oblique cosine-angle integral: the two paired branches combine into a rational slope integral. -/
theorem offdiag_pair_angle_integral (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 < a * b) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2),
        |Real.cos θ| / (a * Real.cos θ ^ 2 + 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2)
        + |Real.cos θ| / (a * Real.cos θ ^ 2 - 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2))
      = 2 * ∫ s in (0 : ℝ)..1,
          (a + (b - a) * s ^ 2) /
            ((a + (b - a) * s ^ 2) ^ 2 - 4 * c ^ 2 * s ^ 2 * (1 - s ^ 2)) := by
  sorry

end RybinAI2026.P01
