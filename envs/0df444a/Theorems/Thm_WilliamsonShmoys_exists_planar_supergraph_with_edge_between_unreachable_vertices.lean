-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_between_unreachable_vertices
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_edge_between_unreachable_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:49:52.821988+00:00
-- url     : https://prove2.me/theorems/f5566c16-ad1a-4dc9-9719-9b410e9d0ed0
-- title:
--   Planar edge augmentation between components
-- statement:
--   For a finite graph with a crossing-free drawing, if two vertices are unreachable from one another, there is a drawable supergraph containing the original graph and the edge between those vertices. This isolates the one-edge geometric augmentation needed by the target; the parent derives strictness from the new edge and unreachability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_with_edge_between_unreachable_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hUnreach : Not (G.Reachable u v)) :
    Exists fun H : SimpleGraph V =>
      And (G <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H) (H.Adj u v)) := by
  sorry
