-- Prove2me | Theorems.Thm_hasPlanarDrawingOn_mono__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
-- name    : hasPlanarDrawingOn_mono__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:46:24.09599+00:00
-- url     : https://prove2.me/theorems/c6d9cfc1-a1d5-436c-8889-0f8fb04ae933
-- title:
--   Planar drawing is preserved by taking subgraphs
-- statement:
--   If a graph on a fixed finite ordered vertex type has a crossing-free drawing, every subgraph on the same vertex type also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem hasPlanarDrawingOn_mono__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hHG : H ≤ G)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
