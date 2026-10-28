-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_across_components
-- name    : WilliamsonShmoys.planar_add_edge_across_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:33:56.490968+00:00
-- url     : https://prove2.me/theorems/75e69d1e-0bf0-4546-b559-b03915650135
-- title:
--   Add an edge between unreachable vertices while preserving planarity
-- statement:
--   For a graph with the specified planar drawing, any pair of unreachable vertices can be joined by a new edge in a strict planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_add_edge_across_components
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (hNotReachable : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Adj u v := by sorry
