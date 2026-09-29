-- Prove2me | Theorems.Thm_MetricGeometry_eq_midpoint_of_isMidpoint
-- name    : MetricGeometry.eq_midpoint_of_isMidpoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T18:30:45.032161+00:00
-- url     : https://prove2.me/theorems/91377928-6aa4-47de-b5d6-839b66c45da0
-- title:
--   A metric midpoint in an inner product space is the linear midpoint
-- statement:
--   Let $E$ be a real inner product space and let $m$ be a *metric* midpoint of $x$ and $y$, that is
--
--   $$
--   d(x,m)=d(m,y)=\tfrac12 d(x,y).
--   $$
--
--   Then $m$ is the linear midpoint, $m=\tfrac12(x+y)$.
--
--   The statement is not a triviality: metric midpoints are defined by two distance equations and could a priori be a large set. What rules that out is strict convexity of the norm. Writing $a=x-m$ and $b=m-y$, the hypotheses say $\|a\|=\|b\|=\tfrac12\|x-y\|$, while $a+b=x-y$, so
--
--   $$
--   \|a+b\|=\|a\|+\|b\| .
--   $$
--
--   Expanding both sides by the polarization identity turns this into $\langle a,b\rangle=\|a\|\,\|b\|$, equality in Cauchy–Schwarz, which forces $a$ and $b$ to be parallel; since they also have equal norms, $a=b$, that is $x-m=m-y$.
--
--   This is the bridge between the synthetic and the linear notion of midpoint, and it is what lets one verify a synthetic curvature condition in a concrete inner product space by a computation with the parallelogram law.
-- source:
--   Synthetic metric geometry of nonpositively curved spaces. The CN inequality is due to F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe); see also M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter II.1 (CAT(0) spaces and convexity of the metric) and Definition I.5.6 (the k-cone over a metric space). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

theorem eq_midpoint_of_isMidpoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (m x y : E) (h : IsMidpoint m x y) :
    m = midpoint ℝ x y := by sorry

end MetricGeometry
