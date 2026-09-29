-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_reparam
-- name    : MetricGeometry.alexandrovAngle_reparam
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T02:00:49.260845+00:00
-- url     : https://prove2.me/theorems/e648263b-54ae-4658-b7f2-50005b162f80
-- title:
--   The Alexandrov angle is invariant under rescaling the parameters
-- statement:
--   The Alexandrov angle is unchanged by rescaling the parameters of the two curves: for all $a,b>0$,
--
--   $$\angle\bigl(t\mapsto g(at),\ t\mapsto h(bt)\bigr)\ =\ \angle(g,h).$$
--
--   **Role.** The Alexandrov angle is written as a functional of two parametrised curves, but it is meant to be an
--   invariant of the pair of *germs* they define at the common initial point. This statement is one half of that:
--   the value does not see a change of speed. In particular the angle between two geodesic segments is the same
--   whether they are parametrised on $[0,1]$ proportionally to arclength or by arclength itself, so results proved
--   under one normalisation transfer to the other without rework.
--
--   That transfer is what is needed to build the space of directions. Its points are germs of geodesic segments at
--   $p$, and the natural representative of a germ is the arclength parametrisation, whereas a geodesic segment
--   $[p,y]$ arrives normalised on $[0,1]$ with speed $d(p,y)$; the two differ by exactly the rescaling above.
--
--   **The argument.** By definition the angle is a $\limsup$ over the product of two copies of the filter of
--   right-hand neighbourhoods of $0$, and rescaling the curves precomposes the function with the map
--   $(s,t)\mapsto(as,bt)$. Multiplication by a positive constant is a homeomorphism of $\mathbb{R}$ preserving
--   $(0,\infty)$, so it pushes the filter $\mathcal{N}_{>0}$ forward to itself; taking products, the map
--   $(s,t)\mapsto(as,bt)$ pushes the product filter forward to itself. A $\limsup$ of a composition is the $\limsup$
--   along the pushed-forward filter, so the two values agree.
-- source:
--   The parametrisation-independence implicit in Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles), where the Alexandrov angle is introduced for geodesic paths and immediately treated as an invariant of the germs at the common initial point.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_reparam {X : Type*} [PseudoMetricSpace X] (p : X)
    (g h : ℝ → X) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    alexandrovAngle p (fun t => g (a * t)) (fun t => h (b * t))
      = alexandrovAngle p g h := by sorry

end MetricGeometry
