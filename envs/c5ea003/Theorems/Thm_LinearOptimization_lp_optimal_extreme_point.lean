-- Prove2me | Theorems.Thm_LinearOptimization_lp_optimal_extreme_point
-- name    : LinearOptimization.lp_optimal_extreme_point
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:55:13.475292+00:00
-- url     : https://prove2.me/theorems/b8eac8d5-ea37-4b3a-827e-db3bda6cdeee
-- title:
--   Some optimal solution is an extreme point
-- statement:
--   **(Theorem 2.7)** Consider the linear programming problem of minimizing $c'x$ over a polyhedron $P$. Suppose that $P$ has at least one extreme point and that there exists an optimal solution.
--
--   Then, there exists an optimal solution which is an extreme point of $P$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.7, p. 65

import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_Polyhedron


/-- **B&T Theorem 2.7 (p. 65).** If the feasible polyhedron has an extreme
point and the LP has an optimal solution, then some extreme point is
optimal. -/

theorem LinearOptimization.lp_optimal_extreme_point {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hext : (Set.extremePoints ℝ (polyhedron A b)).Nonempty)
    (hopt : ∃ x, IsLpOptimal c (polyhedron A b) x) :
    ∃ x ∈ Set.extremePoints ℝ (polyhedron A b),
      IsLpOptimal c (polyhedron A b) x := by
  sorry
