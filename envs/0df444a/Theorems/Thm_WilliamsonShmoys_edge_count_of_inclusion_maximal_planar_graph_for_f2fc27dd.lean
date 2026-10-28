-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_planar_graph_for_f2fc27dd
-- name    : WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_graph_for_f2fc27dd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:25:28.272996+00:00
-- url     : https://prove2.me/theorems/195acd84-fd5c-4c13-a5a5-81ba44b3ad19
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertex type has exactly `3 * |V| - 6` edges. Maximality forces the planar embedding to be a triangulation; Euler’s formula then gives the count. This child carries the topological part of the argument and preserves the vertex lower bound and drawing hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_graph_for_f2fc27dd
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
