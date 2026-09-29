-- Prove2me | Theorems.Thm_LinearOptimization_simplex_reduced_cost_optimality
-- name    : LinearOptimization.simplex_reduced_cost_optimality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:23:14.03478+00:00
-- url     : https://prove2.me/theorems/564a979b-0eec-47dd-8d80-f7fdb55cc68e
-- title:
--   Reduced-cost optimality conditions
-- statement:
--   **(Theorem 3.1)** Consider a basic feasible solution $x$ associated with a basis matrix $B$, and let $\bar{c}$ be the corresponding vector of reduced costs.
--
--   - **(a)** If $\bar{c} \ge 0$, then $x$ is optimal.
--   - **(b)** If $x$ is optimal and nondegenerate, then $\bar{c} \ge 0$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 3.1, p. 86

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_ReducedCost


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 3.1 (p. 86).** Reduced-cost optimality conditions at a
basic feasible solution `x` associated with the basis `B`: (a) if every
reduced cost is nonnegative, `x` is optimal; (b) if `x` is optimal and
nondegenerate, every reduced cost is nonnegative. -/

theorem LinearOptimization.simplex_reduced_cost_optimality {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (x : Fin n → ℝ) (hx : x ∈ stdPolyhedron A b)
    (hxB : ∀ j ∉ Set.range B, x j = 0) :
    ((∀ j, 0 ≤ reducedCost A c B j) → IsLpOptimal c (stdPolyhedron A b) x) ∧
    (IsLpOptimal c (stdPolyhedron A b) x →
      ¬IsStdDegenerateBasicSolution A b x →
      ∀ j, 0 ≤ reducedCost A c B j) := by
  sorry
