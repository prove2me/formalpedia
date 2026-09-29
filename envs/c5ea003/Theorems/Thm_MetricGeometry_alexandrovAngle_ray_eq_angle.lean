-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_ray_eq_angle
-- name    : MetricGeometry.alexandrovAngle_ray_eq_angle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T22:51:43.802421+00:00
-- url     : https://prove2.me/theorems/f8e7b85c-3488-49a7-9fc9-131760fb27bf
-- title:
--   The Alexandrov angle between two rays is the Euclidean angle
-- statement:
--   Let $E$ be a real inner product space, $p\in E$, and $u,v\in E$. The two rays $t\mapsto p+tu$ and $t\mapsto p+tv$ issue from $p$, and their Alexandrov angle is the ordinary angle between their direction vectors:
--
--   $$
--   \angle_p\bigl(t\mapsto p+tu,\ t\mapsto p+tv\bigr)\;=\;\angle(u,v)\;=\;\arccos\frac{\langle u,v\rangle}{\|u\|\,\|v\|}.
--   $$
--
--   **Role.** This is the consistency check that justifies the name. The Alexandrov angle is a purely metric construction: it uses only distances, and it is defined in every metric space. The theorem says that when the metric space happens to be a Euclidean (or Hilbert) space, the construction returns the angle that linear algebra already assigns to the two directions, so nothing has been lost or distorted in passing from the linear to the metric setting. It is also the base case of every comparison argument: a curvature bound is a comparison between the actual upper angle of a configuration and the angle of the corresponding Euclidean model, and this theorem is what identifies the latter.
--
--   The statement carries no nondegeneracy hypothesis. If $u=0$, both sides equal $\pi/2$ — the value that the degenerate quotient $0/0$ produces on either side — so the identity holds unconditionally.
-- source:
--   Standard metric geometry. The Alexandrov (upper) angle is Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319; its behaviour on a geodesic line is Remark I.1.13(2), the value in a metric tree is Remark I.1.13(3), and the triangle inequality making it a pseudometric is Proposition I.1.14. Proposition II.3.1 shows that in a CAT(k) space the defining limit superior is a limit. The space of directions is treated in Chapter II.3. Mathlib has no comparison angle and no angle between curves.

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_eq_angle

namespace MetricGeometry

theorem alexandrovAngle_ray_eq_angle {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p u v : E) :
    alexandrovAngle p (fun t => p + t • u) (fun t => p + t • v)
      = InnerProductGeometry.angle u v := by sorry

end MetricGeometry
