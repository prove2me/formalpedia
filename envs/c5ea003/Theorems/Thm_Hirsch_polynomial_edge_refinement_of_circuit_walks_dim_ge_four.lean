-- Prove2me | Theorems.Thm_Hirsch_polynomial_edge_refinement_of_circuit_walks_dim_ge_four
-- name    : Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-10T23:02:38.493841+00:00
-- url     : https://prove2.me/theorems/73beca40-31bc-42d5-8350-5ec9ac28bd3e
-- title:
--   Polynomial edge refinement of circuit walks in dimension at least four
-- statement:
--   This is the high-dimensional remainder of circuit-to-edge refinement for the polynomial Hirsch conjecture.
--
--   There exist constants $C,k\in\mathbb{N}$ such that the following holds. Let $d\ge 4$ and let $P\subseteq\mathbb{R}^d$ be a bounded H-polytope cut out by an irredundant, strictly feasible family of $n$ linear inequalities. Whenever $u$ and $v$ are vertices of $P$ joined by a padded maximal row-circuit walk of length $L$, there is a padded vertex-edge walk of $P$ from $u$ to $v$ of length
--
--   $$
--   C(n+d)^k L.
--   $$
--
--   The replacement walk need not visit the original circuit intermediates, which may fail to be vertices. It need not be monotone in any linear functional, and it need not preserve every already visited facet.
--
--   In ambient dimension at most three, Klee's theorem already supplies the linear graph-diameter bound $n-d$, which is a polynomial circuit-to-edge overhead. The hypothesis $d\ge 4$ therefore isolates the remaining content of the unrestricted circuit-to-edge refinement statement. Constant or dimension-only overhead per circuit step is already false for polygons; the present statement still allows polynomial row-dependent overhead.
--
--   **Formalization Note** The Lean statement uses the same circuit-walk and irredundancy vocabulary as `Hirsch.polynomial_edge_refinement_of_circuit_walks`, with the additional hypothesis $4\le d$. Walks are padded: each step is either stationary or an edge, and the budget is an exact natural-number length.
-- source:
--   Restriction of Prove2Me theorem Hirsch.polynomial_edge_refinement_of_circuit_walks (open circuit-to-edge refinement leaf of the polynomial Hirsch conjecture; motivation arXiv:2602.06958v2, no literature-priority claim). Complementary low-dimensional case: V. Klee, Convex polytopes and linear programming, Proc. IBM Sci. Comput. Symp. Combin. Probl. (1966); recorded as Hirsch.dimension_three_bound.

import Definitions.Def_Hirsch_circuit_model
set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

theorem Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      4 ≤ d →
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      Hirsch.RowPresentationIrredundant a b → Hirsch.StrictlyFeasibleRows a b →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ L : ℕ, Hirsch.RowCircuitWalk a b L u v →
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k * L) = v ∧
          ∀ j < C * (n + d) ^ k * L,
            w j = w (j + 1) ∨
              Hirsch.Adj (Hirsch.Hpoly a b) (w j) (w (j + 1)) := by sorry
