-- Prove2me | Theorems.Thm_LinearOptimization_lp_extreme_point_optimality
-- name    : LinearOptimization.lp_extreme_point_optimality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:55:22.083081+00:00
-- url     : https://prove2.me/theorems/0a249075-c31d-42a4-8825-f7ec69cd85d8
-- title:
--   Extreme-point optimality: optimal cost $-\infty$ or an optimal extreme point
-- statement:
--   **(Theorem 2.8, GOAL)** Consider the linear programming problem of minimizing $c'x$ over a polyhedron $P$. Suppose that $P$ has at least one extreme point.
--
--   Then, either the optimal cost is equal to $-\infty$, or there exists an extreme point which is optimal.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.8, p. 66

import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_Polyhedron


/-- **B&T Theorem 2.8 (p. 66).** Over a polyhedron with at least one extreme
point, either the optimal cost is `−∞` or some extreme point is optimal. -/

theorem LinearOptimization.lp_extreme_point_optimality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hext : (Set.extremePoints ℝ (polyhedron A b)).Nonempty) :
    lpValue c (polyhedron A b) = ⊥ ∨
      ∃ x ∈ Set.extremePoints ℝ (polyhedron A b),
        IsLpOptimal c (polyhedron A b) x := by
  sorry
