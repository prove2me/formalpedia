-- Prove2me | Theorems.Thm_RybinAI2026_P01_one_sphere_two_point_of_cross_excess
-- name    : RybinAI2026.P01.one_sphere_two_point_of_cross_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T22:42:34.72806+00:00
-- url     : https://prove2.me/theorems/a8284b25-5997-4257-8744-302ae2b4dfa5
-- title:
--   Cross-excess condition implies the cleared one-sphere two-point inequality
-- statement:
--   Let FA, FB, FC be real functions on any type.  If FC is nonnegative, FC <= FA and FC <= FB pointwise, and the cross-excess condition (1/4) FC z FC w <= (FA z - FC z)(FB w - FC w) holds for every pair z, w, then FC z^2 FB w^2 + FC w^2 FA z^2 <= FA z^2 FB w^2 holds for every pair.  This is pure real algebra: with p = FC z, q = FC w, a = FA z - FC z >= 0 and b = FB w - FC w >= 0 the difference of the two sides equals a*b*(4pq + 2pb + 2aq + ab) - p^2*q^2, and the cross-excess condition is 4ab >= pq, so that difference is nonnegative.  Instantiating FA, FB, FC with the directional spherical integrals turns the last hypothesis into the published strengthening one_sphere_cross_excess and the conclusion into the two-point form one_sphere_two_point; the monotonicity hypotheses are the proved directional_integral_add_denominator_mono and the nonnegativity is the proved directional_integral_pos.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484.  Algebraic core of the cross-excess reduction of the one-sphere two-point leaf (19a0d89c); the exact slack identity is (p+a)^2(q+b)^2 - p^2(q+b)^2 - q^2(p+a)^2 = ab(4pq+2pb+2aq+ab) - p^2 q^2.

import Mathlib

namespace RybinAI2026.P01

/-- The algebraic heart of the one-sphere two-point reduction: positivity, two one-slot
monotonicity bounds, and the cross-excess condition already imply the cleared two-point
inequality. -/
theorem one_sphere_two_point_of_cross_excess {ι : Type*} (FA FB FC : ι → ℝ)
    (hFC : ∀ z, 0 ≤ FC z)
    (hmonoA : ∀ z, FC z ≤ FA z)
    (hmonoB : ∀ z, FC z ≤ FB z)
    (hcross : ∀ z w, (1 / 4) * (FC z * FC w) ≤ (FA z - FC z) * (FB w - FC w)) :
    ∀ z w : ι, FC z ^ 2 * FB w ^ 2 + FC w ^ 2 * FA z ^ 2 ≤ FA z ^ 2 * FB w ^ 2 := by sorry

end RybinAI2026.P01
