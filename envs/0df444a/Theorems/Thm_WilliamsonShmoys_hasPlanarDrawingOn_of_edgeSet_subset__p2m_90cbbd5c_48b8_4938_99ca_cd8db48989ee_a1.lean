-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_edgeSet_subset__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:04:16.087682+00:00
-- url     : https://prove2.me/theorems/fd8a1f2d-df19-46bd-abb0-0c150f438229
-- title:
--   Planar drawing passes to an edge subgraph
-- statement:
--   If H has a crossing-free drawing and G uses only edges of H, then G has a crossing-free drawing using the same vertex positions and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : Set.Subset G.edgeSet H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
