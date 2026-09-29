-- Prove2me | Theorems.Thm_LinearOptimization_lp_optimal_cost_convex_in_rhs
-- name    : LinearOptimization.lp_optimal_cost_convex_in_rhs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T21:06:00.613896+00:00
-- url     : https://prove2.me/theorems/946496c6-027e-4671-ae5c-6ca1e348b82a
-- title:
--   Convexity of the optimal cost in the right-hand side $b$
-- statement:
--   **(Theorem 5.1, p. 213)** The optimal cost $F(b)$ is a convex function of $b$ on the set $S$.
--
--   (Standing hypotheses in force, made explicit: standard form with the rows of $A$ linearly independent, and the dual feasible set $\{p \mid p'A \le c'\}$ nonempty — so that $F(b)$ is finite for every $b \in S$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 5.1, p. 213 (standing assumptions pp. 202, 212)

import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_OptimalCostFunction


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 5.1 (p. 213).** The optimal cost `F(b)` of the standard
form problem `min c'x, Ax = b, x ≥ 0` (rows of `A` linearly independent,
dual feasible set nonempty) is a convex function of `b` on the set `S` of
feasible right-hand sides. -/

theorem LinearOptimization.lp_optimal_cost_convex_in_rhs {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (F : (Fin m → ℝ) → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (hdual : (dualFeasibleStd A c).Nonempty)
    (hF : ∀ b ∈ feasibleRhsSet A, ((F b : ℝ) : EReal) = lpOptimalCostRhs A c b) :
    ConvexOn ℝ (feasibleRhsSet A) F := by
  sorry
