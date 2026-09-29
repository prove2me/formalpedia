-- Prove2me | Theorems.Thm_MetricGeometry_cos_comparisonAngle
-- name    : MetricGeometry.cos_comparisonAngle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T00:06:21.524746+00:00
-- url     : https://prove2.me/theorems/b131a3e0-8e6d-436d-8a25-b062b76bf141
-- title:
--   The cosine of the comparison angle is the law-of-cosines quotient
-- statement:
--   For three points $p,x,y$ of a metric space with $p$ distinct from $x$ and from $y$,
--
--   $$
--   \cos\widetilde\angle_p(x,y)=\frac{d(p,x)^2+d(p,y)^2-d(x,y)^2}{2\,d(p,x)\,d(p,y)} .
--   $$
--
--   **Role.** The comparison angle is *defined* as the arccosine of the right-hand side, so this identity is not a tautology: it says the quotient actually lies in $[-1,1]$, which is where $\arccos$ inverts $\cos$. That in turn is exactly the triangle inequality, twice. The quotient is at most $1$ iff $|d(p,x)-d(p,y)|\le d(x,y)$, and at least $-1$ iff $d(x,y)\le d(p,x)+d(p,y)$.
--
--   In geometric terms this is the statement that a Euclidean comparison triangle exists: any three numbers satisfying the triangle inequality are the side lengths of a genuine triangle in the plane, and $\widetilde\angle_p(x,y)$ is its angle at the vertex corresponding to $p$. Every quantitative use of comparison angles goes through this identity, because it is the only way to get back from the angle to the distances.
-- source:
--   Standard comparison geometry: any triple of points of a metric space has a Euclidean comparison triangle. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, I.2.13 (the law of cosines in Euclidean space) and Lemma I.2.14 (existence of comparison triangles). Mathlib has the law of cosines for an inner product space but no comparison angle and no metric-space form.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem cos_comparisonAngle {X : Type*} [PseudoMetricSpace X] (p x y : X)
    (hx : dist p x ≠ 0) (hy : dist p y ≠ 0) :
    Real.cos (comparisonAngle p x y)
      = (dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2) / (2 * dist p x * dist p y) := by sorry

end MetricGeometry
