-- Prove2me | Theorems.Thm_LinearOptimization_max_flow_ford_fulkerson_integer_termination
-- name    : LinearOptimization.max_flow_ford_fulkerson_integer_termination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:36:35.950714+00:00
-- url     : https://prove2.me/theorems/4275f55c-b0ac-4b85-bac8-1bb1cf9c4ea4
-- title:
--   Integrality and finite termination of the Ford–Fulkerson algorithm
-- statement:
--   **(Bertsimas & Tsitsiklis, Theorem 7.8, p. 305)** Suppose that all arc capacities $u_{ij}$ are integer or infinite, and that the Ford–Fulkerson algorithm is initialized with an integer flow vector.
--
--   Then, the arc flow variables remain integer throughout the algorithm and, if the optimal value is finite, the algorithm terminates after a finite number of steps.
--
--   *Encoding:* (Formalized over the run predicate: every flow in every admissible Ford–Fulkerson run started at an integer feasible flow is integer, and if the maximum flow value is finite, there is no infinite admissible run — for every augmenting-path selection rule.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 7.8, p. 305

import Definitions.Def_LinearOptimization_AugmentingPath


open Matrix
open scoped ENNReal

/-- **Bertsimas & Tsitsiklis, Theorem 7.8 (p. 305).** For integer-or-infinite capacities and
an integer initial feasible flow: every flow produced by the
Ford–Fulkerson algorithm is integer, and if the maximum flow value is
finite there is no infinite admissible run — under every
augmenting-path selection rule. -/

theorem LinearOptimization.max_flow_ford_fulkerson_integer_termination {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (u : Fin m → ℝ≥0∞) (s t : Fin n)
    (hst : s ≠ t) (hloop : HasNoSelfLoops arcs) (hupos : ∀ k, 0 < u k)
    (huint : ∀ k, u k = ⊤ ∨ ∃ z : ℕ, u k = (z : ℝ≥0∞))
    (f₀ : Fin m → ℝ) (hf₀ : IsFeasibleMaxFlow arcs u s t f₀)
    (hint₀ : ∀ k, ∃ z : ℤ, f₀ k = (z : ℝ)) :
    (∀ f, Relation.ReflTransGen (IsFordFulkersonStep arcs u s t) f₀ f →
      ∀ k, ∃ z : ℤ, f k = (z : ℝ)) ∧
    (maxFlowValue arcs u s t ≠ ⊤ →
      ¬∃ g : ℕ → Fin m → ℝ, g 0 = f₀ ∧
        ∀ i, IsFordFulkersonStep arcs u s t (g i) (g (i + 1))) := by
  sorry
