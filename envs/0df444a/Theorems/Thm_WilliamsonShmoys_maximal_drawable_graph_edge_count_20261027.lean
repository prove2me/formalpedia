-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_20261027
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:32:28.195915+00:00
-- url     : https://prove2.me/theorems/7c0ff52e-d9dd-4e1f-abde-6c468b4aa191
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable graphs on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hGmax : ∀ K : SimpleGraph V, G.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ G.edgeSet) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
