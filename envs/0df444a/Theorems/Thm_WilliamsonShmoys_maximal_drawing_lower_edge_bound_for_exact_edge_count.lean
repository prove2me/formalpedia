-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_lower_edge_bound_for_exact_edge_count
-- name    : WilliamsonShmoys.maximal_drawing_lower_edge_bound_for_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:25:15.211717+00:00
-- url     : https://prove2.me/theorems/158ccbf6-3ca0-48ad-8600-1558f143b58e
-- title:
--   Edge lower bound for an inclusion-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex type has at least three times its vertex count minus six edges. The proof route is to show that a planar drawing of a nonmaximal planar graph admits an additional edge on the existing vertex set, then use maximality to conclude that the embedding is a triangulation; Euler’s formula and triangular faces yield the bound. The vertex-count hypothesis excludes the small cases where the standard maximal-planar edge formula does not apply. This is the main topological obligation remaining for the parent theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_lower_edge_bound_for_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
