-- Prove2me | Definitions.Def_space_of_directions
-- name    : space_of_directions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-31T07:48:29.002832+00:00
-- url     : https://prove2.me/theorems/43f8f712-6e4b-40fa-98c1-1e98eedcee84
-- title:
--   Geodesic germs and the angle between them
-- statement:
--   The space of directions $\Sigma_pX$ of a metric space $X$ at a point $p$ is the set of germs at $p$ of nonconstant geodesic segments issuing from $p$, equipped with the Alexandrov angle as its metric; for a Hadamard space one then passes to the metric quotient and its completion.
--
--   This file records the two ingredients. A **geodesic germ at $p$** is a geodesic segment $\gamma$ with $\gamma(0)=p$ and $\gamma(1)$ at positive distance from $p$, bundled with that endpoint and the two conditions. The **angle between two germs** is the Alexandrov (upper) angle
--   $$\angle_p(\gamma_1,\gamma_2)=\limsup_{s,t\downarrow0}\ \widetilde\angle_p\bigl(\gamma_1(s),\gamma_2(t)\bigr).$$
--
--   **Role.** Almost everything in the local geometry of a nonpositively curved space is a statement about $\Sigma_p$: for a Euclidean building it is a spherical building, and the image of a small circle under a homogeneous harmonic map, rescaled, becomes a closed local geodesic in it — which is what makes it a billiards path in the model chamber and ultimately forces the order of the map to be rational. Recording germs and the angle between them is the first step: the angle is a pseudometric on germs, and the space of directions is the associated metric space.
--
--   **Formalization note.** The nondegeneracy condition is stated as $d(p,\gamma(1))\ne0$ rather than $\gamma(1)\ne p$ so that it makes sense in a pseudometric space; in a metric space the two agree. Germs are represented by segments rather than by equivalence classes, so the angle is only a pseudometric — two segments may subtend angle zero without being equal — and the space of directions is its quotient.
-- source:
--   The space of directions Sigma_p X of a CAT(0) space, M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Grundlehren 319, Springer 1999, Part II, Chapter 3, Definition 3.18; for buildings, B. Kleiner and B. Leeb, Publ. Math. IHES 86 (1997), Section 4.1.2.

import Mathlib
import Definitions.Def_metric_alexandrov_angle

/-!
# Geodesic germs and the space of directions

The space of directions `Σ_p X` of a metric space at a point `p` is the set of
germs at `p` of nonconstant geodesic segments issuing from `p`, with the
Alexandrov angle as its metric.  This file records the germs and the angle
between them; that the angle is a pseudometric is proved separately, and the
space of directions proper is its metric quotient (and, for a Hadamard space,
the completion of that).

Mathlib has no notion of a geodesic in a metric space and no space of
directions.
-/

namespace MetricGeometry

universe u

/-- A geodesic germ at `p`: a geodesic segment issuing from `p` and ending at
a point at positive distance from `p`. -/
structure GeodesicGerm {X : Type u} [PseudoMetricSpace X] (p : X) where
  /-- The parametrized segment. -/
  toFun : ℝ → X
  /-- Its far endpoint. -/
  endpoint : X
  /-- It is a geodesic segment from `p` to that endpoint. -/
  isSegment : IsGeodesicSegment toFun p endpoint
  /-- The germ is nondegenerate. -/
  nondegenerate : dist p endpoint ≠ 0

/-- The angle between two geodesic germs at `p`, that is, the distance in the
space of directions at `p`. -/
noncomputable def germAngle {X : Type u} [PseudoMetricSpace X] {p : X}
    (g1 g2 : GeodesicGerm p) : ℝ :=
  alexandrovAngle p g1.toFun g2.toFun

end MetricGeometry


