-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_eq_of_comparisonAngle_const
-- name    : MetricGeometry.alexandrovAngle_eq_of_comparisonAngle_const
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T22:51:26.348125+00:00
-- url     : https://prove2.me/theorems/d8b599ac-9f36-4a58-841f-862f9d7391dd
-- title:
--   A constant comparison angle computes the Alexandrov angle
-- statement:
--   The Alexandrov angle at $p$ between two curves $g_1,g_2$ is defined as a limit superior,
--
--   $$
--   \angle_p(g_1,g_2)=\limsup_{s,t\to0^+}\widetilde\angle_p\bigl(g_1(s),g_2(t)\bigr),
--   $$
--
--   and a limit superior is not, in general, computed by evaluating the function at any particular point. This lemma records the one case in which it is: if the comparison angle $\widetilde\angle_p(g_1(s),g_2(t))$ takes a single value $c$ for *all* strictly positive parameters $s,t$, then
--
--   $$
--   \angle_p(g_1,g_2)=c .
--   $$
--
--   **Role.** This is the workhorse for every explicit computation of an Alexandrov angle. All of the model configurations — two rays in a Euclidean space, the two halves of a geodesic line, a geodesic ray against itself — have comparison angles that are exactly scale-invariant, hence constant on $(0,\infty)^2$, so their Alexandrov angles are read off directly. It is also the precise statement of the informal principle that in a cone, where the comparison angle does not depend on how far out one looks, the upper angle is an honest angle rather than a limit.
--
--   **Formalization Note.** The limit superior is taken along the product filter $\mathcal N_{>0}(0)\times\mathcal N_{>0}(0)$, which is nontrivial, and on which the hypothesis makes the integrand eventually equal to the constant $c$; the conclusion then follows from the value of a limit superior of a constant along a nontrivial filter.
-- source:
--   Standard metric geometry. The Alexandrov (upper) angle is Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319; its behaviour on a geodesic line is Remark I.1.13(2), the value in a metric tree is Remark I.1.13(3), and the triangle inequality making it a pseudometric is Proposition I.1.14. Proposition II.3.1 shows that in a CAT(k) space the defining limit superior is a limit. The space of directions is treated in Chapter II.3. Mathlib has no comparison angle and no angle between curves.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_eq_of_comparisonAngle_const {X : Type*} [PseudoMetricSpace X]
    (p : X) (g1 g2 : ℝ → X) (c : ℝ)
    (h : ∀ s t : ℝ, 0 < s → 0 < t → comparisonAngle p (g1 s) (g2 t) = c) :
    alexandrovAngle p g1 g2 = c := by sorry

end MetricGeometry
