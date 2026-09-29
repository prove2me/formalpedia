-- Prove2me | Theorems.Thm_LinearOptimization_lp_attains_or_unbounded
-- name    : LinearOptimization.lp_attains_or_unbounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:55:29.788013+00:00
-- url     : https://prove2.me/theorems/495173f6-9c3d-45fb-9440-747a3d0a2cb0
-- title:
--   Attainment of the optimal cost in linear programming
-- statement:
--   **(Corollary 2.3)** Consider the linear programming problem of minimizing $c'x$ over a nonempty polyhedron.
--
--   Then, either the optimal cost is equal to $-\infty$ or there exists an optimal solution.
--
--   (The book contrasts this with nonlinear problems: minimizing $1/x$ subject to $x \ge 1$ has finite optimal cost but no optimal solution.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 2.3, p. 67

import Definitions.Def_Polyhedron


/-- **B&T Corollary 2.3 (p. 67).** An LP over a nonempty polyhedron either
has optimal cost `−∞` or attains an optimal solution. -/

theorem LinearOptimization.lp_attains_or_unbounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hne : (polyhedron A b).Nonempty) :
    lpValue c (polyhedron A b) = ⊥ ∨ ∃ x, IsLpOptimal c (polyhedron A b) x := by
  sorry
