-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_maximal_drawing_graph_584c8b76
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_graph_584c8b76
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:59:30.335721+00:00
-- url     : https://prove2.me/theorems/917ea052-d8fb-40ee-8590-e1f6659747f0
-- title:
--   Lower edge bound from drawing maximality
-- statement:
--   An inclusion-maximal graph with the supplied planar drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_graph_584c8b76
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
