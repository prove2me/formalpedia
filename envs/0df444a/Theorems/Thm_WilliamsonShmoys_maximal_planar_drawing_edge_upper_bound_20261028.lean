-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound_20261028
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:54:04.605732+00:00
-- url     : https://prove2.me/theorems/5cf6dc66-fbcd-4290-b27d-09838fedac0d
-- title:
--   Edge bound for an edge-maximal planar drawing
-- statement:
--   A drawable finite simple graph with at least three vertices and no drawable proper supergraph has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hMax : ∀ G : SimpleGraph V, H.edgeSet ⊆ G.edgeSet →
      HasPlanarDrawingOn G → G.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
