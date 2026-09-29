-- Prove2me | Theorems.Thm_ConvexOptimization_dualCone_inner_pos_of_mem_interior
-- name    : ConvexOptimization.dualCone_inner_pos_of_mem_interior
-- status  : Proved
-- author  : @jianglsbz
-- created : 2026-08-15T04:46:23.012659+00:00
-- url     : https://prove2.me/theorems/5bc44df5-1b6e-4a7d-ae29-f53c2d64e004
-- title:
--   A nonzero dual vector is strictly positive on the interior of the cone
-- statement:
--   Membership in the dual cone $K^{*} = \{y : \langle x, y\rangle \ge 0 \ \text{ for all } x \in K\}$ only guarantees a nonstrict inequality against points of $K$. On the *interior* of $K$ the inequality is automatically strict, provided the dual vector is nonzero: if $z \in K^{*}$ with $z \ne 0$ and $w \in \operatorname{int} K$, then
--
--   $$\langle w, z\rangle > 0.$$
--
--   The reason is that an interior point can be moved a little *against* $z$ and stay inside $K$. Suppose $\langle w, z\rangle = 0$. Since $w$ is interior, some ball $B(w, \varepsilon)$ is contained in $K$, so with $\delta = \varepsilon / (2 \lVert z\rVert) > 0$ the point $w - \delta z$ still lies in $K$; its distance to $w$ is $\delta \lVert z\rVert = \varepsilon / 2 < \varepsilon$. But then
--
--   $$\langle w - \delta z,\, z\rangle = \langle w, z\rangle - \delta \lVert z\rVert^{2} = -\delta \lVert z\rVert^{2} < 0,$$
--
--   contradicting $z \in K^{*}$.
--
--   Both hypotheses are needed. For $z = 0$ the pairing vanishes. And on the boundary of $K$ a nonzero element of $K^{*}$ may well pair to zero — that is exactly what a hyperplane supporting $K$ at that point does.
--
--   This is the strict form underlying the recorded property that $K^{*}$ is pointed whenever $K$ has nonempty interior. In conic duality it is the step that rules out a degenerate multiplier: a Slater point lies in $\operatorname{int} K$, so pairing it against a nonzero dual vector cannot vanish.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 51-53, §2.6.1, eq. (2.19) (dual cone) and the dual-cone property list

import Mathlib
import Definitions.Def_dualCone

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.dualCone_inner_pos_of_mem_interior {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (z w : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ dualCone K) (hzne : z ≠ 0) (hw : w ∈ interior K) :
    0 < ⟪w, z⟫ := by sorry
