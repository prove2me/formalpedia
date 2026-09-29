-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_eq_zero_of_between
-- name    : MetricGeometry.comparisonAngle_eq_zero_of_between
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T00:24:18.972428+00:00
-- url     : https://prove2.me/theorems/f1f7bf76-f6c2-4258-929d-07f211c562d9
-- title:
--   A degenerate triangle has comparison angle zero
-- statement:
--   If $y$ lies metrically between $x$ and $z$, that is $d(x,y)+d(y,z)=d(x,z)$, and $y,z$ are both distinct from $x$, then
--
--   $$
--   \widetilde\angle_x(y,z)=0 .
--   $$
--
--   **Role.** The comparison triangle of a triple satisfying the triangle inequality with equality is degenerate: it collapses onto a segment, and the angle at the vertex between the two shorter sides is zero. This is the metric statement that a point of a geodesic segment determines the same direction from the endpoint as the far endpoint does, expressed purely in terms of distances and without any geodesic being mentioned.
--
--   It is the first thing one needs when checking that a direction assignment on segments is consistent: the direction of $\overline{xz}$ and of $\overline{xy}$ must agree when $y$ lies on $\overline{xz}$, and in an axiomatization where directions are controlled by comparison angles, this is what makes the two agree.
--
--   The computation is immediate: substituting $d(y,z)=d(x,z)-d(x,y)$ into the law-of-cosines quotient gives exactly $1$, and $\arccos 1=0$.
-- source:
--   Elementary comparison geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, I.2.13 (the law of cosines in Euclidean space) and Lemma I.2.14 (existence of comparison triangles).

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem comparisonAngle_eq_zero_of_between {X : Type*} [PseudoMetricSpace X] (x y z : X)
    (hxy : dist x y ≠ 0) (hxz : dist x z ≠ 0)
    (hbetween : dist x y + dist y z = dist x z) :
    comparisonAngle x y z = 0 := by sorry

end MetricGeometry
