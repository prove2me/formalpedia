-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_geodesicLine_opposite_eq_pi
-- name    : MetricGeometry.alexandrovAngle_geodesicLine_opposite_eq_pi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T22:51:52.636044+00:00
-- url     : https://prove2.me/theorems/6a43d432-1dd8-486e-af87-bcedd00d0835
-- title:
--   The two halves of a geodesic line meet at angle $\pi$
-- statement:
--   Let $\gamma:\mathbb R\to X$ be a geodesic line in a metric space, so $d(\gamma(s),\gamma(t))=|s-t|$ for all $s,t$. Its two halves issuing from $\gamma(0)$, namely $t\mapsto\gamma(t)$ and $t\mapsto\gamma(-t)$ for $t>0$, satisfy
--
--   $$
--   \angle_{\gamma(0)}\bigl(\gamma(\cdot),\ \gamma(-\cdot)\bigr)=\pi .
--   $$
--
--   **Role.** A geodesic line is the metric model of a straight line, and the theorem says that the upper angle detects straightness: two directions are opposite exactly when the points on them are as far apart as the triangle inequality permits, $d(\gamma(s),\gamma(-t))=s+t$, which forces the comparison angle to be $\arccos(-1)=\pi$ at every pair of parameters. Together with the bound $\angle\le\pi$, this shows $\pi$ is attained, so the space of directions at a point of a space containing a geodesic line has diameter exactly $\pi$; the pair of opposite directions is the metric counterpart of a pair of antipodal points of a sphere. In the building setting these are the endpoints of a wall, and their being antipodal is what makes the space of directions a *spherical* building rather than merely a metric space of diameter $\pi$.
-- source:
--   Standard metric geometry. The Alexandrov (upper) angle is Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319; its behaviour on a geodesic line is Remark I.1.13(2), the value in a metric tree is Remark I.1.13(3), and the triangle inequality making it a pseudometric is Proposition I.1.14. Proposition II.3.1 shows that in a CAT(k) space the defining limit superior is a limit. The space of directions is treated in Chapter II.3. Mathlib has no comparison angle and no angle between curves.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_geodesicLine_opposite_eq_pi {X : Type*} [PseudoMetricSpace X]
    (gamma : ℝ → X) (h : IsGeodesicLine gamma) :
    alexandrovAngle (gamma 0) gamma (fun t => gamma (-t)) = Real.pi := by sorry

end MetricGeometry
