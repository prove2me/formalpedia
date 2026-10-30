-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count_v2
-- name    : WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:07:16.620631+00:00
-- url     : https://prove2.me/theorems/6ee91510-964c-4246-8db1-a793199be835
-- title:
--   Exact edge count of a maximal planar graph
-- statement:
--   A graph with a planar drawing that is maximal among planar supergraphs on the same finite vertex type has exactly `3n − 6` edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
