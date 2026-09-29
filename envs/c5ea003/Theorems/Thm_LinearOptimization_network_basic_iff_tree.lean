-- Prove2me | Theorems.Thm_LinearOptimization_network_basic_iff_tree
-- name    : LinearOptimization.network_basic_iff_tree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T21:59:50.462104+00:00
-- url     : https://prove2.me/theorems/d02e3130-4e11-44ab-a511-81c14f7650ac
-- title:
--   Basic solutions are exactly tree solutions
-- statement:
--   **(Bertsimas & Tsitsiklis, Theorem 7.4, p. 283)** A flow vector is a basic solution if and only if it is a tree solution.
--
--   (Setting: the uncapacitated network flow problem in standard form with constraints $\tilde{\mathbf{A}}\mathbf{f}=\tilde{\mathbf{b}}$, $\mathbf{f}\ge 0$, under standing Assumption 7.1: $\sum_{i\in\mathcal{N}}b_i=0$ and $G$ connected. 'Basic solution' is in the sense of Bertsimas & Tsitsiklis, Definition 2.9 / Mission I's BasicSolution; consequently a feasible tree solution is a basic feasible solution, p. 283.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 7.4, p. 283

import Definitions.Def_LinearOptimization_TreeSolution
import Definitions.Def_BasicSolution


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 7.4 (p. 283).** For the uncapacitated network flow
problem `Ãf = b̃`, `f ≥ 0` on a connected graph with `∑ᵢ bᵢ = 0`, a flow
vector is a basic solution (in the Definition 2.9 sense, for the truncated
standard-form constraint system) if and only if it is a tree solution. -/

theorem LinearOptimization.network_basic_iff_tree {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) (bsupply : Fin (n + 1) → ℝ)
    (hloop : HasNoSelfLoops arcs) (hconn : IsConnectedNetwork arcs)
    (hsum : ∑ i, bsupply i = 0) (f : Fin m → ℝ) :
    IsBasicSolution
        (stdFormSystem (truncatedIncidence arcs) (truncatedSupply bsupply)) f ↔
      IsTreeSolution arcs bsupply f := by
  sorry
