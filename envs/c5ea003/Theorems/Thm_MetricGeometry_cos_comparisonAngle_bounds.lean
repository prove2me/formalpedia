-- Prove2me | Theorems.Thm_MetricGeometry_cos_comparisonAngle_bounds
-- name    : MetricGeometry.cos_comparisonAngle_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T00:18:06.329734+00:00
-- url     : https://prove2.me/theorems/a0f9a54d-d5fa-40cf-a112-003007e6cdee
-- title:
--   Two-sided estimate for the cosine of a comparison angle
-- statement:
--   Let $p,x,y$ be points of a metric space with $d(p,x)=s>0$ and $d(p,y)=t>0$, and write $u=d(x,y)$. Then
--
--   $$
--   \frac{t-u}{s}\ \le\ \cos\widetilde\angle_p(x,y)\ \le\ \frac{t-u}{s}+\frac{s}{2t}.
--   $$
--
--   **Role.** The comparison angle is what one can compute from distances, but its cosine is a quotient in which $s$ appears both alone and squared, and it is not obvious how it behaves as $s$ shrinks with $t$ held fixed. This estimate answers that: the cosine is pinned to $\frac{t-u}{s}$ within an error of $\frac{s}{2t}$, which vanishes as $s\to0$. So the asymptotics of the comparison angle along a geodesic issuing from $p$ are governed by the single quantity $\frac{t-d(x,y)}{s}$ — a difference quotient of the distance to the fixed point $y$.
--
--   That is exactly what is needed to compare the two natural definitions of the angle between geodesics at $p$: the Alexandrov angle, in which both parameters tend to $0$, and the strong upper angle, in which only one of them does. The estimate lets the second be reduced to the first, and hence shows the two notions agree.
--
--   Both bounds come from the same identity: subtracting $\frac{t-u}{s}$ from the law-of-cosines quotient leaves $\frac{s^2-(t-u)^2}{2st}$, and the triangle inequality gives $|u-t|\le s$, so that expression is nonnegative and at most $\frac{s}{2t}$. No geodesics and no curvature hypothesis are involved; only three points of a metric space.
-- source:
--   Lemma I.1.17 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles), the technical estimate used to prove Proposition I.1.16 that the strong upper angle agrees with the Alexandrov angle of Definition I.1.12.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem cos_comparisonAngle_bounds {X : Type*} [PseudoMetricSpace X]
    (p x y : X) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hx : dist p x = s) (hy : dist p y = t) :
    (t - dist x y) / s ≤ Real.cos (comparisonAngle p x y) ∧
      Real.cos (comparisonAngle p x y) ≤ (t - dist x y) / s + s / (2 * t) := by sorry

end MetricGeometry
