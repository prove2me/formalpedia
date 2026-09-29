-- Prove2me | Theorems.Thm_LinearOptimization_simplex_pivot_state_cost_decrease
-- name    : LinearOptimization.simplex_pivot_state_cost_decrease
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-06T03:50:41.113013+00:00
-- url     : https://prove2.me/theorems/08181245-f1a2-472a-a3b8-b64c1664a3f3
-- title:
--   Strict objective decrease under a nondegenerate simplex pivot
-- statement:
--   Consider the standard-form linear program $\min\{c^{\mathsf T}x:Ax=b,\ x\ge 0\}$. Assume the rows of $A$ are linearly independent, $(B,x)$ is a simplex state, and every basic feasible solution is nondegenerate. If $(B′,x′)$ is obtained from $(B,x)$ by one admissible simplex pivot (negative reduced cost, positive pivot entry, and the minimum-ratio rule), then
--
--   $$
--   (B′,x′)\text{ is again a simplex state},\qquad c^{\mathsf T}x′<c^{\mathsf T}x.
--   $$
--
--   Thus every pivot in a nondegenerate simplex run makes strict objective progress. This is the local descent fact used to rule out cycling by finiteness of the set of bases.
--
--   **Formalization Note** A simplex state records a valid standard basis, feasibility, and zero coordinates outside that basis; `IsSimplexPivot` packages the entering/leaving indices and the minimum-ratio update.
-- source:
--   Dimitris Bertsimas and John N. Tsitsiklis, Introduction to Linear Optimization (Athena Scientific, 1997), Theorem 3.2, p. 89, and proof of Theorem 3.3, p. 91.

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot

open Matrix

theorem LinearOptimization.simplex_pivot_state_cost_decrease {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B B' : Fin m ↪ Fin n) (x x' : Fin n → ℝ)
    (hstate : IsSimplexState A b B x)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬IsStdDegenerateBasicSolution A b y)
    (hpivot : IsSimplexPivot A c B x B' x') :
    IsSimplexState A b B' x' ∧ c ⬝ᵥ x' < c ⬝ᵥ x := by
  sorry
