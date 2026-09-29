-- Prove2me | Theorems.Thm_MetricGeometry_isMidpoint_geodesic_half
-- name    : MetricGeometry.isMidpoint_geodesic_half
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T21:26:35.231264+00:00
-- url     : https://prove2.me/theorems/34807c29-4592-45d5-a076-7ee58861986f
-- title:
--   The midpoint of a geodesic segment is a metric midpoint
-- statement:
--   The parameter value $\tfrac12$ of a geodesic segment is a metric midpoint of its endpoints: if $\gamma$ is a geodesic from $x$ to $y$, then
--
--   $$
--   d\bigl(x,\gamma(\tfrac12)\bigr)=d\bigl(\gamma(\tfrac12),y\bigr)=\tfrac12 d(x,y).
--   $$
--
--   This is the defining identity of a geodesic evaluated at the two pairs $(0,\tfrac12)$ and $(\tfrac12,1)$, in both cases giving the factor $|{\cdot}|=\tfrac12$.
--
--   **Why record it.** It is the bridge between the two notions. Midpoints are the primitive in the synthetic curvature condition, which is stated so as to make sense in a space with no geodesics at all; geodesics are the primitive in every statement about the shape of a space. This lemma lets a result proved about midpoints — uniqueness under nonpositive curvature, convexity of the distance, the projection theorem — be applied at the parameter $\tfrac12$ of a geodesic without re-deriving anything.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (geodesics), I.2.13 (the law of cosines in Euclidean space), Lemma I.2.14 (existence of comparison triangles), and Proposition II.1.4(1) (uniqueness of geodesics in a CAT(0) space). The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem isMidpoint_geodesic_half {X : Type*} [PseudoMetricSpace X]
    (g : ℝ → X) (x y : X) (h : IsGeodesicSegment g x y) :
    IsMidpoint (g (1 / 2)) x y := by sorry

end MetricGeometry
