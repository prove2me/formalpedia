-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_geodesicSegment_self_eq_zero
-- name    : MetricGeometry.alexandrovAngle_geodesicSegment_self_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T02:03:41.783422+00:00
-- url     : https://prove2.me/theorems/396fe88a-07dd-4708-bb7a-ae6db9ef997d
-- title:
--   A nondegenerate geodesic segment makes angle zero with itself
-- statement:
--   A nondegenerate geodesic segment makes angle zero with itself: if $g$ is a geodesic segment from $p$ to $y$ and
--   $d(p,y)\neq0$, then
--
--   $$\angle(g,g)=0 .$$
--
--   **Role.** Together with the symmetry of the Alexandrov angle and the triangle inequality, this is what makes
--   "defining the same direction at $p$" — the relation $\angle(g,h)=0$ — reflexive, and hence an equivalence
--   relation on the geodesic segments issuing from $p$. The quotient by that relation, metrised by the angle, is the
--   space of directions $\Sigma_pX$; without reflexivity there is no quotient to speak of.
--
--   The nondegeneracy hypothesis is necessary, and its failure is not a technicality: if $y=p$ the segment is
--   constant, every comparison angle in the defining $\limsup$ is $\arccos(0/0)=\pi/2$ by the convention used for a
--   degenerate vertex, and the angle is $\pi/2$ rather than $0$. Constant segments therefore have to be excluded
--   from the space of directions, which is why its points are indexed by geodesic segments $[p,y]$ with $y\neq p$.
--
--   **The argument.** The comparison angle is identically $0$ on the relevant range. For $s,t\in(0,1)$, writing
--   $D=d(p,y)>0$, the constant-speed parametrisation gives $d(p,g(s))=sD$, $d(p,g(t))=tD$ and
--   $d(g(s),g(t))=|s-t|D$, so the law-of-cosines quotient is
--
--   $$\frac{s^2D^2+t^2D^2-(s-t)^2D^2}{2\,sD\,tD}=\frac{2stD^2}{2stD^2}=1,$$
--
--   and $\arccos 1=0$. Since $(0,1)\times(0,1)$ belongs to the filter along which the defining $\limsup$ is taken,
--   that $\limsup$ agrees with the $\limsup$ of the constant function $0$, which is $0$.
-- source:
--   The reflexivity half of the remark following Proposition I.1.14 in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1: the triangle inequality for angles implies that the relation given by vanishing of the Alexandrov angle is an equivalence relation on the geodesics issuing from a point.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_geodesicSegment_self_eq_zero {X : Type*} [PseudoMetricSpace X]
    (p y : X) (g : ℝ → X) (hg : IsGeodesicSegment g p y) (hy : dist p y ≠ 0) :
    alexandrovAngle p g g = 0 := by sorry

end MetricGeometry
