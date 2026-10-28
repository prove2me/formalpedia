-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_components
-- name    : WilliamsonShmoys.planar_drawing_add_edge_across_components
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T05:09:24.24218+00:00
-- url     : https://prove2.me/theorems/98c75cad-973f-4110-bf57-1a6d4c4b2049
-- title:
--   Extend a planar drawing across disconnected components
-- statement:
--   For a finite ordered graph with a planar drawing that is disconnected, choose two nonadjacent vertices and extend the graph to a planar-drawn supergraph containing the edge between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_add_edge_across_components
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Adj u v ∧
      ∃ H : SimpleGraph V,
        G ≤ H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
