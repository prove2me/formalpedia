-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_edge_from_components
-- name    : WilliamsonShmoys.planar_drawing_insert_edge_from_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:15:14.417202+00:00
-- url     : https://prove2.me/theorems/c2a497b0-0886-48fb-a8c8-80700f0d36f6
-- title:
--   Insert an edge between distinct components of a planar drawing
-- statement:
--   For a finite ordered vertex type, if a graph has a planar drawing and two distinct vertices are in different reachability components, extend the graph by exactly the edge joining them while retaining planarity. The resulting edge set is precisely the old edge set with that edge inserted, and the inserted edge was absent from the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_insert_edge_from_components
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (huv : u ≠ v)
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ G' : SimpleGraph V,
      G ≤ G' ∧ G'.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn G' ∧
      G'.edgeSet = insert s(u, v) G.edgeSet ∧
      s(u, v) ∉ G.edgeSet := by sorry
