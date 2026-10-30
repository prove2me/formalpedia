-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_edge_count
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:42:01.08086+00:00
-- url     : https://prove2.me/theorems/6274f47d-124c-4fd1-84e6-71540a951a1f
-- title:
--   Planar augmentation to the maximal planar edge count
-- statement:
--   Every simple graph with a crossing-free drawing on a finite ordered vertex set of size at least three is a subgraph of a graph on that same vertex set that also has a crossing-free drawing and exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
