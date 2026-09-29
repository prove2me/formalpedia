-- Prove2me | Definitions.Def_metric_geodesic_angle
-- name    : metric_geodesic_angle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-27T21:17:49.119117+00:00
-- url     : https://prove2.me/theorems/3d93fa43-1521-4b9d-a8cb-6818899cdfea
-- title:
--   Geodesic segments and comparison angles
-- statement:
--   Mathlib has no notion of a geodesic in a metric space and no comparison angle. This file supplies both, on top of the midpoint and curvature definitions.
--
--   **Geodesic segments.** A geodesic from $x$ to $y$ is an isometric parametrization of an interval, normalized to $[0,1]$ so that the parameter is proportional to arclength:
--
--   $$
--   \gamma(0)=x,\qquad \gamma(1)=y,\qquad d\bigl(\gamma(s),\gamma(t)\bigr)=|s-t|\,d(x,y)\ \ \text{for }s,t\in[0,1].
--   $$
--
--   The normalization makes the definition parametrization-independent up to the obvious reparametrization and keeps the endpoints as explicit data.
--
--   **Comparison angles.** Given three points $p,x,y$, the comparison angle at $p$ is the angle at the corresponding vertex of a Euclidean triangle with the same three side lengths, read off from the law of cosines:
--
--   $$
--   \widetilde\angle_p(x,y)=\arccos\frac{d(p,x)^2+d(p,y)^2-d(x,y)^2}{2\,d(p,x)\,d(p,y)} .
--   $$
--
--   Comparison angles are the basic device of Alexandrov geometry: curvature bounds are stated by comparing the actual geometry of a triangle with that of its Euclidean comparison triangle, and the Alexandrov angle between two geodesics issuing from a point is the limit of comparison angles along them.
--
--   When $p$ coincides with $x$ or with $y$ the defining quotient degenerates to $0/0$, which Lean evaluates to $0$, giving the value $\pi/2$. Nothing is claimed at such degenerate triangles; the notion is used at genuine ones, and every statement about it here either holds vacuously or carries a nondegeneracy hypothesis.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren 319, Chapter I.1 (geodesics) and Chapter I.2 / II.1 (comparison triangles and the Alexandrov angle). Mathlib has no geodesic in a metric space and no comparison angle; it has InnerProductGeometry.angle only for vectors in an inner product space.

import Mathlib
import Definitions.Def_metric_npc_cone

/-!
# Geodesic segments and comparison angles

Mathlib has no notion of a geodesic in a metric space, and no comparison
angle.  Both are supplied here, on top of the midpoint and curvature
definitions.

A geodesic segment is an isometric parametrization of an interval, normalized
to the unit interval so that the parameter is proportional to arclength.  The
comparison angle at `p` in the triangle `p x y` is the angle at the
corresponding vertex of a Euclidean triangle with the same three side lengths,
obtained from the law of cosines.
-/

namespace MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

/-- A geodesic segment from `x` to `y`, parametrized on the unit interval
proportionally to arclength. -/
def IsGeodesicSegment (gamma : ℝ → X) (x y : X) : Prop :=
  gamma 0 = x ∧ gamma 1 = y ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (gamma s) (gamma t) = |s - t| * dist x y

/-- The Euclidean comparison angle at `p` in the triangle with vertices
`p`, `x`, `y`, defined by the law of cosines.  When `p` coincides with `x` or
`y` the defining quotient is `0 / 0 = 0` and the value is `π / 2`; the
comparison angle is only used at genuine triangles. -/
noncomputable def comparisonAngle (p x y : X) : ℝ :=
  Real.arccos
    ((dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2) / (2 * dist p x * dist p y))

end MetricGeometry


