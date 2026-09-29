-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_scale
-- name    : MetricGeometry.comparisonAngle_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T21:20:03.093403+00:00
-- url     : https://prove2.me/theorems/e5cf2872-43a6-4073-9905-5367608bdcb3
-- title:
--   Comparison angles at the vertex of a metric cone are scale-invariant
-- statement:
--   In a metric cone, comparison angles at the vertex are invariant under dilation: for $\lambda>0$ and points $p,q$,
--
--   $$
--   \widetilde\angle_{\mathsf O}\bigl(\lambda p,\lambda q\bigr)=\widetilde\angle_{\mathsf O}(p,q),
--   $$
--
--   where $\mathsf O$ is the vertex.
--
--   The proof is a computation once one observes that the vertex is fixed by every dilation: $\lambda\cdot\mathsf O=\lambda\cdot(0\cdot p)=(\lambda\cdot 0)\cdot p=0\cdot p=\mathsf O$. Consequently all three side lengths of the triangle scale by $\lambda$,
--
--   $$
--   d(\mathsf O,\lambda p)=\lambda\, d(\mathsf O,p),\qquad
--   d(\lambda p,\lambda q)=\lambda\, d(p,q),
--   $$
--
--   so numerator and denominator of the law-of-cosines quotient both acquire a factor $\lambda^2$, which cancels because $\lambda\ne0$.
--
--   The hypothesis $\lambda>0$ cannot be dropped: at $\lambda=0$ both points collapse to the vertex and the quotient degenerates, giving $\pi/2$ irrespective of the original angle.
--
--   **Mathematical role.** Scale invariance is the reason cones are the right receptacle for tangent objects. A blow-up procedure rescales the target, and any quantity defined through comparison angles at the vertex — the angle between two geodesic germs, the space of directions, homogeneity of a map of a given order — is unaffected by that rescaling, so it descends to the tangent cone.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (geodesics), I.2.13 (the law of cosines in Euclidean space), Lemma I.2.14 (existence of comparison triangles), and Proposition II.1.4(1) (uniqueness of geodesics in a CAT(0) space). The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem comparisonAngle_scale {X : Type*} [PseudoMetricSpace X]
    (K : ConeStructure X) (lam : ℝ) (hlam : 0 < lam) (p q : X) :
    comparisonAngle K.vertex (K.scale lam p) (K.scale lam q)
      = comparisonAngle K.vertex p q := by sorry

end MetricGeometry
