-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_subset_drawable
-- name    : WilliamsonShmoys.edge_subset_drawable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:47:45.152592+00:00
-- url     : https://prove2.me/theorems/fe74eda8-d390-4d60-b00e-8aa34f4b242e
-- title:
--   Subgraphs of drawable graphs are drawable
-- statement:
--   If a simple graph's edges are a subset of the edges of a graph with a planar drawing, then it also has a planar drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_subset_drawable
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
