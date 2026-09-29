-- Prove2me | Theorems.Thm_MetricGeometry_geodesicSegment_unique_of_isNPC
-- name    : MetricGeometry.geodesicSegment_unique_of_isNPC
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T21:19:53.298618+00:00
-- url     : https://prove2.me/theorems/b35b530a-68a1-4555-b1be-a98bd44e16ea
-- title:
--   Geodesics are unique in a nonpositively curved space
-- statement:
--   In a metric space with midpoints satisfying the CN inequality, geodesic segments are unique: if $\gamma_1$ and $\gamma_2$ are geodesics from $x$ to $y$, then $\gamma_1(t)=\gamma_2(t)$ for every $t\in[0,1]$.
--
--   **The argument.** Write $D=d(x,y)$ and fix $t$. Both geodesics satisfy
--
--   $$
--   d(\gamma_i(t),x)=tD,\qquad d(\gamma_i(t),y)=(1-t)D .
--   $$
--
--   Let $m$ be a midpoint of $\gamma_1(t)$ and $\gamma_2(t)$. Midpoint convexity of the metric gives $d(m,x)\le tD$ and $d(m,y)\le(1-t)D$, while the triangle inequality gives $d(m,x)+d(m,y)\ge D$. Since the two upper bounds sum to exactly $D$, both must be equalities; in particular $d(m,x)=tD$.
--
--   Now apply the curvature inequality to the midpoint $m$ with free point $x$:
--
--   $$
--   (tD)^2=d(m,x)^2\le\tfrac12(tD)^2+\tfrac12(tD)^2-\tfrac14 d\bigl(\gamma_1(t),\gamma_2(t)\bigr)^2
--   =(tD)^2-\tfrac14 d\bigl(\gamma_1(t),\gamma_2(t)\bigr)^2 ,
--   $$
--
--   so $d(\gamma_1(t),\gamma_2(t))^2\le0$ and the two points coincide.
--
--   **Remarks.** No dyadic subdivision or continuity argument is needed: the squeeze that pins $d(m,x)$ to $tD$ does all the work, and the curvature inequality then has no room left. The hypothesis that midpoints exist is used only to produce $m$; uniqueness of midpoints is not assumed and is in fact a special case, obtained at $t=\tfrac12$.
--
--   Uniqueness of geodesics is the first structural consequence of nonpositive curvature and is what makes constructions such as geodesic homotopy, convexity of the metric along geodesics and the contraction of the projection onto a convex set well defined.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (geodesics), I.2.13 (the law of cosines in Euclidean space), Lemma I.2.14 (existence of comparison triangles), and Proposition II.1.4(1) (uniqueness of geodesics in a CAT(0) space). The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem geodesicSegment_unique_of_isNPC {X : Type*} [MetricSpace X]
    (hnpc : IsNPC X) (hmid : HasMidpoints X)
    (g1 g2 : ℝ → X) (x y : X) (h1 : IsGeodesicSegment g1 x y)
    (h2 : IsGeodesicSegment g2 x y) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    g1 t = g2 t := by sorry

end MetricGeometry
