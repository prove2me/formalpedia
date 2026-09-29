-- Prove2me | Theorems.Thm_MetricGeometry_eVariationOn_eq_of_isLocalGeodesicWithSpeed
-- name    : MetricGeometry.eVariationOn_eq_of_isLocalGeodesicWithSpeed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:01:19.686985+00:00
-- url     : https://prove2.me/theorems/9006450c-696f-4a5e-85b5-d926d6dc8fbd
-- title:
--   The length of a local geodesic of speed $k$ over $[a,b]$ is $k(b-a)$
-- statement:
--   Let $c:\mathbb R\to X$ be a local geodesic of speed $k$ and scale $\delta>0$ in a metric space, and let $a\le b$. Then the length of $c$ over $[a,b]$ — its total variation, the supremum of $\sum_i d(c(t_{i+1}),c(t_i))$ over all finite increasing subdivisions — is exactly
--
--   $$
--   \operatorname{Length}\bigl(c|_{[a,b]}\bigr)=k\,(b-a).
--   $$
--
--   **Role.** This is the statement that a local geodesic is parametrized proportionally to arclength, with the proportionality constant $k$, and it is the point at which a purely local metric hypothesis becomes a global quantitative one. Both inequalities use the local hypothesis, but in opposite directions: the upper bound comes from the global Lipschitz estimate that the local identity implies, applied to an arbitrary subdivision, whose sum then telescopes; the lower bound comes from *one* particular subdivision, the uniform one of mesh at most $\delta$, on which every term of the sum is computed exactly by the defining identity.
--
--   Length is what converts the local geometry of a curve into an invariant one can compare across spaces. In the setting of harmonic maps into a Euclidean building, the image of a small circle under a homogeneous map of order $\alpha$ is a closed local geodesic of speed $\alpha L$, and its length $2\pi\alpha L$ is the quantity that must be matched against the lengths available in the space of directions — a spherical building — which is what constrains $\alpha$ to a rational number with controlled denominator.
--
--   **Formalization Note.** The length is `eVariationOn c (Set.Icc a b)`, Mathlib's extended-real-valued total variation.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 for geodesics, local geodesics and the length of a curve, and Proposition II.1.4(2) for local geodesics in CAT(0) spaces. Mathlib has `eVariationOn` but no notion of a local geodesic and no computation of the length of one.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

theorem eVariationOn_eq_of_isLocalGeodesicWithSpeed {X : Type*} [PseudoMetricSpace X]
    (c : ℝ → X) (k delta : ℝ) (h : IsLocalGeodesicWithSpeed c k delta)
    (a b : ℝ) (hab : a ≤ b) :
    eVariationOn c (Set.Icc a b) = ENNReal.ofReal (k * (b - a)) := by sorry

end MetricGeometry
