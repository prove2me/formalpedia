-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_a41ba058_0926_4932_8131_302826679a62_a2
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_a41ba058_0926_4932_8131_302826679a62_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:17.973666+00:00
-- url     : https://prove2.me/theorems/b938225d-5398-4163-8cf9-4c859a32fb13
-- title:
--   Planar drawing inherited by subgraphs
-- statement:
--   If `H` has a crossing-free drawing on the given ordered vertex type and `G` is a subgraph of `H`, then `G` has the same drawing. Restrict the edge-indexed conditions to the edges of `G`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_a41ba058_0926_4932_8131_302826679a62_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
