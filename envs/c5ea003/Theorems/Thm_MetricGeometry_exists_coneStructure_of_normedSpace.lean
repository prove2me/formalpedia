-- Prove2me | Theorems.Thm_MetricGeometry_exists_coneStructure_of_normedSpace
-- name    : MetricGeometry.exists_coneStructure_of_normedSpace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T18:31:18.343699+00:00
-- url     : https://prove2.me/theorems/6add8d85-5d09-4db7-8a7c-e4c8f462cca9
-- title:
--   A real normed space is a metric cone with vertex $0$
-- statement:
--   Every real normed space carries a metric cone structure with vertex the origin and dilation the scalar action:
--
--   $$
--   \lambda\cdot p=\lambda p,\qquad
--   d(\lambda p,\lambda q)=\lambda\,d(p,q)\quad(\lambda\ge0).
--   $$
--
--   The verification is immediate from homogeneity of the norm, $\|\lambda(p-q)\|=|\lambda|\,\|p-q\|$, together with $1\cdot p=p$, $0\cdot p=0$ and associativity of the scalar action.
--
--   The point of recording it is not difficulty but non-vacuity. A metric cone is an axiomatic structure, and statements quantifying over cones — homogeneity of a map of a given order, the tangent cone at a point of a nonpositively curved space, the cone over a spherical building — are only meaningful once a supply of examples is available. Normed spaces are the basic supply, and every cone locally looks like one in the flat case.
-- source:
--   Synthetic metric geometry of nonpositively curved spaces. The CN inequality is due to F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe); see also M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter II.1 (CAT(0) spaces and convexity of the metric) and Definition I.5.6 (the k-cone over a metric space). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

theorem exists_coneStructure_of_normedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    ∃ K : ConeStructure E, K.vertex = 0 ∧
      ∀ (lam : ℝ) (p : E), K.scale lam p = lam • p := by sorry

end MetricGeometry
