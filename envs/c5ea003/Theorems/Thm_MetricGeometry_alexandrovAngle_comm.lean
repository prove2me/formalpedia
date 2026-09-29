-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_comm
-- name    : MetricGeometry.alexandrovAngle_comm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:00:59.140367+00:00
-- url     : https://prove2.me/theorems/42715def-90c1-44f8-aec2-6de9fed6f1de
-- title:
--   The Alexandrov angle is symmetric
-- statement:
--   For any two curves $g_1,g_2$ issuing from a point $p$ of a metric space,
--
--   $$
--   \angle_p(g_1,g_2)=\angle_p(g_2,g_1).
--   $$
--
--   **Role.** Together with the vanishing of the self-angle on a geodesic, this is the second of the pseudometric axioms for the Alexandrov angle on the set of geodesics issuing from $p$, and hence one of the two facts that make the space of directions at $p$ a metric space rather than merely a set with a numerical pairing.
--
--   The symmetry is inherited from that of the comparison angle, but it is not immediate: the two sides are limit superiors of *different* functions of the pair $(s,t)$, taken along the same product filter. What identifies them is that interchanging the two arms of every comparison angle amounts to precomposing the integrand with the coordinate swap of $\mathbb R^2$, and the product filter $\mathcal N_{>0}(0)\times\mathcal N_{>0}(0)$, having equal factors, is carried to itself by that swap.
-- source:
--   Standard metric geometry. The Alexandrov (upper) angle is Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319; its behaviour on a geodesic line is Remark I.1.13(2), the value in a metric tree is Remark I.1.13(3), and the triangle inequality making it a pseudometric is Proposition I.1.14. Proposition II.3.1 shows that in a CAT(k) space the defining limit superior is a limit. The space of directions is treated in Chapter II.3. Mathlib has no comparison angle and no angle between curves.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_comm {X : Type*} [PseudoMetricSpace X] (p : X) (g1 g2 : ℝ → X) :
    alexandrovAngle p g1 g2 = alexandrovAngle p g2 g1 := by sorry

end MetricGeometry
