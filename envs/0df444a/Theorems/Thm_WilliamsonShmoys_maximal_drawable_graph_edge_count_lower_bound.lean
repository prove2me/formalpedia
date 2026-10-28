-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:13:58.005564+00:00
-- url     : https://prove2.me/theorems/26cbec15-a016-4bbf-b55b-721eefe9b1c1
-- title:
--   Maximality forces the planar edge bound
-- statement:
--   An inclusion-maximal graph with the supplied planar drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet →
      HasPlanarDrawingOn L → Set.Subset L.edgeSet K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
