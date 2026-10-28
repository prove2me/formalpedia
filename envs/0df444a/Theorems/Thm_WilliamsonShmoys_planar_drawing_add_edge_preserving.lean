-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_preserving
-- name    : WilliamsonShmoys.planar_drawing_add_edge_preserving
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T01:06:52.413117+00:00
-- url     : https://prove2.me/theorems/5ac7d7c8-5eff-43d1-9b5d-57757ac85e63
-- title:
--   Add a planar edge between components
-- statement:
--   For a disconnected finite graph with a planar drawing, add edges while preserving planarity so that every added edge joins vertices from different old components, and at least one such edge is added. The new arc can be routed through the complement of the finite drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_preserving
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hGdisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) := by sorry
