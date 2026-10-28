-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_separated_pair_with_edge_count
-- name    : WilliamsonShmoys.planar_drawing_add_separated_pair_with_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:00:03.97683+00:00
-- url     : https://prove2.me/theorems/3480872b-769d-4abc-84c1-7439f4db55a0
-- title:
--   Extend a planar drawing between separated vertices with exact edge increase
-- statement:
--   Given the packaged drawing and distinct vertices in different reachability components, extend the graph and its drawing so the vertices become adjacent and the edge count increases by exactly one. The new adjacency cannot already be in the original graph, since every edge gives reachability. The parent derives the requested strict inequality from the exact count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_separated_pair_with_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (huv : u ≠ v)
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ G' : SimpleGraph V,
      G ≤ G' ∧ G'.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn G' ∧
      G'.edgeSet.ncard = G.edgeSet.ncard + 1 := by sorry
