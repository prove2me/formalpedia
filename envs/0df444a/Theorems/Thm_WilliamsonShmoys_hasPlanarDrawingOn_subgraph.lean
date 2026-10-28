-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_subgraph
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_subgraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:10:08.270666+00:00
-- url     : https://prove2.me/theorems/5b28d1ca-7d58-4b2f-ac53-01a4ae6201d0
-- title:
--   Planar drawing restricts to a subgraph
-- statement:
--   Any subgraph of a graph with a crossing-free drawing has a crossing-free drawing, using the same vertex placement and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_subgraph
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : Set.Subset G.edgeSet H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
