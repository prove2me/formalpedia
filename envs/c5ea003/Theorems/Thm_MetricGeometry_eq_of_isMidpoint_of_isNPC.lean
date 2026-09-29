-- Prove2me | Theorems.Thm_MetricGeometry_eq_of_isMidpoint_of_isNPC
-- name    : MetricGeometry.eq_of_isMidpoint_of_isNPC
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T18:31:07.964832+00:00
-- url     : https://prove2.me/theorems/07e8965b-ffab-4692-a191-f6766190248b
-- title:
--   Midpoints are unique in a nonpositively curved space
-- statement:
--   In a metric space satisfying the CN inequality, midpoints are unique: if $m$ and $m'$ are both metric midpoints of $x$ and $y$, then $m=m'$.
--
--   The proof is one application of the inequality. Take $z=m'$ and write $d=d(x,y)$. Since $m'$ is a midpoint, $d(x,m')=d(y,m')=d/2$, so the right-hand side of the CN inequality collapses:
--
--   $$
--   d(m,m')^2 \;\le\; \tfrac12\Bigl(\tfrac{d}{2}\Bigr)^2+\tfrac12\Bigl(\tfrac{d}{2}\Bigr)^2-\tfrac{d^2}{4}
--   \;=\;\tfrac{d^2}{4}-\tfrac{d^2}{4}\;=\;0 .
--   $$
--
--   A squared distance is nonnegative, so $d(m,m')=0$ and the two midpoints coincide.
--
--   Uniqueness is what promotes the midpoint relation to an operation, and with it the whole apparatus of geodesics, convexity of the distance function, and projection onto convex sets. Note that no existence assumption is needed: the statement is that there is at most one midpoint, whether or not there is one.
-- source:
--   Synthetic metric geometry of nonpositively curved spaces. The CN inequality is due to F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe); see also M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter II.1 (CAT(0) spaces and convexity of the metric) and Definition I.5.6 (the k-cone over a metric space). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

theorem eq_of_isMidpoint_of_isNPC {X : Type*} [MetricSpace X] (h : IsNPC X)
    (m m' x y : X) (hm : IsMidpoint m x y) (hm' : IsMidpoint m' x y) :
    m = m' := by sorry

end MetricGeometry
