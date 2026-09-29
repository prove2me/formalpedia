-- Prove2me | Theorems.Thm_MetricGeometry_germAngle_pseudoMetric
-- name    : MetricGeometry.germAngle_pseudoMetric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:52:06.373289+00:00
-- url     : https://prove2.me/theorems/755155d8-e5e8-4f59-ab00-92b8be79c58b
-- title:
--   The angle between geodesic germs is a pseudometric of diameter at most pi
-- statement:
--   The Alexandrov angle between geodesic germs at a point $p$ of a metric space is a pseudometric of diameter at most $\pi$: it vanishes on the diagonal, is symmetric, satisfies the triangle inequality, and takes values in $[0,\pi]$.
--
--   **Role.** This is what makes the space of directions $\Sigma_pX$ a metric space: $\Sigma_p$ is by definition the set of germs at $p$ of nonconstant geodesic segments issuing from $p$, and the angle is its distance. Only after this is established can one speak of geodesics in $\Sigma_p$, of $\Sigma_p$ being a spherical building for a Euclidean building $X$, or of a curve in $\Sigma_p$ having constant speed — the language in which the image of a small circle under a homogeneous harmonic map is analysed. The bound $\pi$ on the diameter is the reason a local geodesic of $\Sigma_p$ shorter than $\pi$ is a geodesic.
--
--   **The argument.** Each clause is an instance of a known property of the Alexandrov angle. A nondegenerate geodesic segment makes angle $0$ with itself; the angle is symmetric in its arguments; the segment form of the triangle inequality, applied with the middle germ in the distinguished position and combined with symmetry, gives the triangle inequality in the usual order; and the angle, being a limit superior of arccosines, lies in $[0,\pi]$. The nondegeneracy of the germs is what supplies the hypotheses of the first and third.
-- source:
--   The space of directions of a metric space and its angular metric, M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Grundlehren 319, Springer 1999, Part II, Chapter 3, Definition 3.18 and Proposition 3.1 (the angle is a metric on the space of directions).

import Definitions.Def_space_of_directions

namespace MetricGeometry

universe u

theorem germAngle_pseudoMetric {X : Type u} [PseudoMetricSpace X] (p : X) :
    (∀ g : GeodesicGerm p, germAngle g g = 0) ∧
    (∀ g1 g2 : GeodesicGerm p, germAngle g1 g2 = germAngle g2 g1) ∧
    (∀ g1 g2 g3 : GeodesicGerm p,
      germAngle g1 g3 ≤ germAngle g1 g2 + germAngle g2 g3) ∧
    (∀ g1 g2 : GeodesicGerm p, germAngle g1 g2 ∈ Set.Icc 0 Real.pi) := by sorry

end MetricGeometry
