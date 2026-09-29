-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_eq_of_comparisonAngle_const_near
-- name    : MetricGeometry.alexandrovAngle_eq_of_comparisonAngle_const_near
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:57:04.307506+00:00
-- url     : https://prove2.me/theorems/000d7ab0-a7a2-4ae5-9211-ae2ade4a7ddb
-- title:
--   The Alexandrov angle is determined by the comparison angles at small parameters
-- statement:
--   Let $g_1,g_2$ be two curves issuing from a point $p$ of a metric space. If the comparison angle
--   $$\widetilde\angle_p\bigl(g_1(s),g_2(t)\bigr)$$
--   takes the constant value $c$ for all $s,t$ in some interval $(0,\varepsilon)$, then the Alexandrov (upper) angle between $g_1$ and $g_2$ at $p$ equals $c$.
--
--   **Role.** The Alexandrov angle is by definition the upper limit of the comparison angles as both parameters tend to $0$ from above, so only arbitrarily small parameters matter. This local form is what is needed in practice: a geodesic segment is parametrised on the unit interval and says nothing about parameters beyond $1$, so a hypothesis quantified over all positive parameters is unusable. With this version one can compute the angle between two segments of a flat — where the comparison angle is constant along them — and thereby verify the angle rigidity axiom of a Euclidean building on its model apartment.
--
--   **The argument.** The set $(0,\varepsilon)$ belongs to the filter of small positive reals, since it is the intersection of $(0,\infty)$ with a neighbourhood of $0$. Hence the hypothesis holds eventually along the product of two copies of that filter, which is the filter defining the Alexandrov angle. The upper limit of a function eventually equal to a constant, along a nontrivial filter, is that constant.
-- source:
--   The definition of the Alexandrov (upper) angle as an upper limit of comparison angles, M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Grundlehren 319, Springer 1999, Part I, Chapter 1, Definition 1.12.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

universe u

theorem alexandrovAngle_eq_of_comparisonAngle_const_near {X : Type u} [PseudoMetricSpace X]
    (p : X) (g1 g2 : ℝ → X) (c eps : ℝ) (heps : 0 < eps)
    (h : ∀ s t : ℝ, 0 < s → s < eps → 0 < t → t < eps →
      comparisonAngle p (g1 s) (g2 t) = c) :
    alexandrovAngle p g1 g2 = c := by sorry

end MetricGeometry
