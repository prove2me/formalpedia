-- Prove2me | Theorems.Thm_BookSixth_round_circle_unit_rescale
-- name    : BookSixth.round_circle_unit_rescale
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T14:12:44.110148+00:00
-- url     : https://prove2.me/theorems/29131552-efe5-4793-b464-c07312a94028
-- title:
--   Chapter 15: rescaling a round circle about its own centre by 1/r
-- statement:
--   Let $C$ be a round circle in three-dimensional space, written in the canonical form $C = \{c + (r\cos t)\,u + (r\sin t)\,v : t \in \mathbb{R}\}$ where $r > 0$ and $u, v$ are orthonormal. Then the pointwise rescaling $S(x) = r^{-1} (x - c) + c$ carries $C$ onto the round circle $C' = \{c + (\cos t)\,u + (\sin t)\,v : t \in \mathbb{R}\}$ of radius one with the same centre $c$ and lying in the same plane spanned by $u, v$.
--
--   This is the algebraic core of the cutoff-rescale construction for the open leaf `BookSixth.roundness_restoration_after_prefix`. That leaf asks for a homeomorphism which fixes every standard circle at time one and whose image of a dragged circle is round again. A global rigid motion cannot do this, because fixing all the standard circles forces a rotation about the $x$-axis, and such a rotation does not straighten a circle lying in a tilted plane. Rescaling about the circle's own centre can.
--
--   The reason this particular identity matters is the Lipschitz budget. The alternative route through `BookSixth.bump_perturbation_is_homeomorph_v4` is provably closed: because the cutoff $\chi_i$ equals $1$ on $C_i$, the perturbation has slope on $C_i$ equal to the on-circle slope of the per-component motion, so demanding a global contraction forces that slope to stay below one at every time, while the landing condition forces the final scale to be exactly $1/r$. Those two demands are compatible only when $r > 1$. A centred rescale carries no such budget and therefore also applies when $r \le 1$, where the motion must expand rather than contract. The radius dependence is precisely the obstruction this leaf removes.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_unit_rescale (c u v : Space3) (r : ℝ) (hr : 0 < r)
    (D : Set Space3)
    (hD : D = Set.range (fun t : ℝ => c + (r * Real.cos t) • u +
      (r * Real.sin t) • v)) :
    (fun x : Space3 => r ⁻¹ • (x - c) + c) '' D
      = Set.range (fun t : ℝ => c + (Real.cos t) • u + (Real.sin t) • v) := by
  sorry
