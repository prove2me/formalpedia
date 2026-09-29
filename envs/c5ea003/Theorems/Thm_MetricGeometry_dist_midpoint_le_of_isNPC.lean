-- Prove2me | Theorems.Thm_MetricGeometry_dist_midpoint_le_of_isNPC
-- name    : MetricGeometry.dist_midpoint_le_of_isNPC
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T20:54:47.228559+00:00
-- url     : https://prove2.me/theorems/6533083b-87cf-4f71-8e35-9b7d3a17e42b
-- title:
--   The distance function is midpoint-convex in a nonpositively curved space
-- statement:
--   In a metric space satisfying the CN inequality of Bruhat and Tits, the distance to a fixed point is midpoint-convex: if $m$ is a metric midpoint of $x$ and $y$, then for every $z$
--
--   $$
--   d(m,z)\;\le\;\tfrac12\bigl(d(x,z)+d(y,z)\bigr).
--   $$
--
--   The curvature condition controls the *squared* distance, so the statement is not merely a restatement of it. Writing $a=d(x,z)$, $b=d(y,z)$ and $c=d(x,y)$, the CN inequality gives $d(m,z)^2\le\tfrac12 a^2+\tfrac12 b^2-\tfrac14 c^2$, while the assertion is $d(m,z)^2\le\tfrac14(a+b)^2$. The gap between the two bounds is
--
--   $$
--   \tfrac14(a+b)^2-\Bigl(\tfrac12 a^2+\tfrac12 b^2-\tfrac14 c^2\Bigr)=\tfrac14\bigl(c^2-(a-b)^2\bigr),
--   $$
--
--   which is nonnegative exactly because $|a-b|\le c$, the reverse triangle inequality. So the statement is the CN inequality combined with the triangle inequality, and neither alone suffices.
--
--   Midpoint convexity of the metric is the first step towards convexity of $t\mapsto d(\gamma(t),z)$ along geodesics, and through it towards convexity of the distance between two geodesics, which is the property that gives nonpositively curved spaces their rigidity.
-- source:
--   Synthetic metric geometry of nonpositively curved spaces. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Proposition II.2.4 (projection onto a complete convex subset of a CAT(0) space) and Chapter II.1 for convexity of the metric. The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has the projection theorem only for Hilbert spaces and no synthetic curvature condition.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

open Filter Topology

theorem dist_midpoint_le_of_isNPC {X : Type*} [PseudoMetricSpace X] (h : IsNPC X)
    (x y m z : X) (hm : IsMidpoint m x y) :
    dist m z ≤ (dist x z + dist y z) / 2 := by sorry

end MetricGeometry
