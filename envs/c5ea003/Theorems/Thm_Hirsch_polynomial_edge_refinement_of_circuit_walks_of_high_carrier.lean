-- Prove2me | Theorems.Thm_Hirsch_polynomial_edge_refinement_of_circuit_walks_of_high_carrier
-- name    : Hirsch.polynomial_edge_refinement_of_circuit_walks_of_high_carrier
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T02:06:32.228469+00:00
-- url     : https://prove2.me/theorems/69a0be2b-0832-4f55-9961-c6e29ae7c5f4
-- title:
--   Polynomial edge refinement of circuit walks with a high-dimensional common face
-- statement:
--   Polynomial edge refinement of circuit walks that contain at least one high-dimensional common face.
--
--   Let $d\ge 4$ and let $P\subseteq\mathbb{R}^d$ be a bounded H-polytope given by an irredundant, strictly feasible family of $n$ inequalities. Suppose $u$ and $v$ are vertices joined by a padded row-circuit walk $w_0,\dots,w_L$ for which some consecutive pair has common-face dimension
--   $$
--   h>3.
--   $$
--   The claim is that there exist constants $C,k$, independent of $d,n,P$ and of the walk, such that $u$ and $v$ are also joined by a padded vertex-edge walk of length $C(n+d)^k L$.
--
--   This is the complementary case to routing through common faces of dimension at most three, which is already reduced to Klee's theorem. The present statement isolates the remaining graph-routing difficulty: a circuit displacement whose common carrier has dimension four or more. Constant or dimension-only overhead per circuit step is already false for polygons; polynomial row-dependent overhead is not ruled out.
--
--   **Formalization Note** The extra hypothesis is existential over the given walk, not a restriction of the ambient polytope. Walks are padded.
-- source:
--   Restriction of Prove2Me theorem Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four to walks containing a consecutive pair of common-face dimension at least four. Complementary low-carrier case: Hirsch.common_face_sequence_route_bound_of_dim_le_three (Klee on common faces). No literature-priority claim.

import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_common_face_geometry
set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

theorem Hirsch.polynomial_edge_refinement_of_circuit_walks_of_high_carrier :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      4 ≤ d →
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      Hirsch.RowPresentationIrredundant a b → Hirsch.StrictlyFeasibleRows a b →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ L : ℕ, ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u → w L = v →
        (∀ j ≤ L, w j ∈ Hirsch.Hpoly a b) →
        (∀ j < L, w j = w (j + 1) ∨ Hirsch.RowCircuitStep a b (w j) (w (j + 1))) →
        (∃ j < L, 3 < HirschCommonFace.commonFaceDim a b (w j) (w (j + 1))) →
        ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
          q 0 = u ∧ q (C * (n + d) ^ k * L) = v ∧
          ∀ j < C * (n + d) ^ k * L,
            q j = q (j + 1) ∨
              Hirsch.Adj (Hirsch.Hpoly a b) (q j) (q (j + 1)) := by sorry
