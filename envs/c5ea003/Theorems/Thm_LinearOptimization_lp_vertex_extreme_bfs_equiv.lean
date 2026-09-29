-- Prove2me | Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
-- name    : LinearOptimization.lp_vertex_extreme_bfs_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:54:26.20175+00:00
-- url     : https://prove2.me/theorems/ea20915a-07e6-4e13-80cf-8dcecf2bb888
-- title:
--   Vertex $=$ extreme point $=$ basic feasible solution
-- statement:
--   **(Theorem 2.3, GOAL)** Let $P$ be a nonempty polyhedron and let $x^* \in P$. Then, the following are equivalent:
--
--   - **(a)** $x^*$ is a vertex;
--   - **(b)** $x^*$ is an extreme point;
--   - **(c)** $x^*$ is a basic feasible solution.
--
--   (Stated for a fixed constraint representation of $P$; the book proves it, without loss of generality, for representations by constraints of the form $a_i'x \ge b_i$ and $a_i'x = b_i$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.3, p. 50

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.List.TFAE
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution


/-- **B&T Theorem 2.3 (p. 50).** For a nonempty polyhedron presented by the
constraint family `C` and `x* ∈ P`: vertex ⟺ extreme point ⟺ basic feasible
solution. -/

theorem LinearOptimization.lp_vertex_extreme_bfs_equiv {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) (x' : Fin n → ℝ)
    (hne : (constraintSet C).Nonempty) (hx : x' ∈ constraintSet C) :
    List.TFAE
      [ IsVertex (constraintSet C) x',
        x' ∈ Set.extremePoints ℝ (constraintSet C),
        IsBasicFeasibleSolution C x' ] := by
  sorry
