-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_three_n_minus_six_edges_target
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_three_n_minus_six_edges_target
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:52:44.859917+00:00
-- url     : https://prove2.me/theorems/c11fbfb2-5669-4f9b-9e63-10213a7fd38f
-- title:
--   The edge count of a maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that has the supplied planar drawing predicate and is maximal among planar supergraphs on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_for_three_n_minus_six_edges_target
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
