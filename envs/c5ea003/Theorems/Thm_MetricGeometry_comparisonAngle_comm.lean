-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_comm
-- name    : MetricGeometry.comparisonAngle_comm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:00:52.324821+00:00
-- url     : https://prove2.me/theorems/937bc4fd-ab44-4ae9-b451-fb5c83931931
-- title:
--   The comparison angle is symmetric in its two arms
-- statement:
--   For any three points $p,x,y$ of a metric space,
--
--   $$
--   \widetilde\angle_p(x,y)=\widetilde\angle_p(y,x).
--   $$
--
--   **Role.** The comparison angle is read off the law of cosines applied to a Euclidean triangle with the same three side lengths as the triple $(p,x,y)$, and the vertex at $p$ does not distinguish between its two adjacent sides. The symmetry is therefore built into the geometry, but it is not syntactically visible in the defining formula, whose numerator and denominator both mention $d(p,x)$ and $d(p,y)$ in a fixed order and whose third side appears as $d(x,y)$ rather than $d(y,x)$. Recording it is what allows the comparison angle, and the Alexandrov angle built from it, to be treated as a symmetric function of a pair of arms — the second pseudometric axiom for the space of directions.
-- source:
--   Standard metric geometry. The Alexandrov (upper) angle is Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319; its behaviour on a geodesic line is Remark I.1.13(2), the value in a metric tree is Remark I.1.13(3), and the triangle inequality making it a pseudometric is Proposition I.1.14. Proposition II.3.1 shows that in a CAT(k) space the defining limit superior is a limit. The space of directions is treated in Chapter II.3. Mathlib has no comparison angle and no angle between curves.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem comparisonAngle_comm {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    comparisonAngle p x y = comparisonAngle p y x := by sorry

end MetricGeometry
