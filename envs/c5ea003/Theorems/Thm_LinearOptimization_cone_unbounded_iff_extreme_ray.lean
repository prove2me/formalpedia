-- Prove2me | Theorems.Thm_LinearOptimization_cone_unbounded_iff_extreme_ray
-- name    : LinearOptimization.cone_unbounded_iff_extreme_ray
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T20:48:08.418069+00:00
-- url     : https://prove2.me/theorems/5424eb49-c261-4bd4-bf68-143200a01668
-- title:
--   Unboundedness over a pointed polyhedral cone via extreme rays
-- statement:
--   **(Theorem 4.13)** Consider the problem of minimizing $c'x$ over a pointed polyhedral cone $C = \{x \in \mathbb{R}^n \mid a_i'x \ge 0,\ i = 1, \dots, m\}$.
--
--   The optimal cost is equal to $-\infty$ if and only if some extreme ray $d$ of $C$ satisfies $c'd < 0$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.13, p. 177

import Definitions.Def_LinearOptimization_RecessionCone


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.13 (p. 177).** Over a pointed polyhedral cone
`C = {x | Ax ≥ 0}`, the optimal cost of `min c'x` is `−∞` iff some
extreme ray `d` of `C` has `c'd < 0`. -/

theorem LinearOptimization.cone_unbounded_iff_extreme_ray {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hpointed : IsPointedCone (polyhedron A 0)) :
    lpValue c (polyhedron A 0) = ⊥ ↔
      ∃ d : Fin n → ℝ, IsExtremeRay A d ∧ c ⬝ᵥ d < 0 := by
  sorry
