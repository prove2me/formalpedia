-- Prove2me | Theorems.Thm_LinearOptimization_separating_hyperplane_polyhedron
-- name    : LinearOptimization.separating_hyperplane_polyhedron
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T18:43:11.841751+00:00
-- url     : https://prove2.me/theorems/bd91ae7d-6f25-4362-a9d8-cc9426c99742
-- title:
--   Separating hyperplane theorem
-- statement:
--   **(Theorem 4.11, separating hyperplane theorem)** Let $S$ be a nonempty closed convex subset of $\mathbb{R}^n$ and let $x^* \in \mathbb{R}^n$ be a vector that does not belong to $S$. Then, there exists some vector $c \in \mathbb{R}^n$ such that
--
--   $$c'x^* < c'x$$
--
--   for all $x \in S$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.11, p. 170

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Matrix.Mul


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.11 (p. 170).** Separating hyperplane theorem: for a
nonempty closed convex `S ⊆ ℝⁿ` and `x* ∉ S` there is a vector `c` with
`c'x* < c'x` for every `x ∈ S`. -/

theorem LinearOptimization.separating_hyperplane_polyhedron {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : S.Nonempty) (hclosed : IsClosed S) (hconv : Convex ℝ S)
    (xstar : Fin n → ℝ) (hx : xstar ∉ S) :
    ∃ c : Fin n → ℝ, ∀ x ∈ S, c ⬝ᵥ xstar < c ⬝ᵥ x := by
  sorry
