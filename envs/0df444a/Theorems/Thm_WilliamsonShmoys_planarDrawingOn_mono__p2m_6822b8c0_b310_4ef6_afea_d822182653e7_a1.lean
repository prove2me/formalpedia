-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
-- name    : WilliamsonShmoys.planarDrawingOn_mono__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:21.414932+00:00
-- url     : https://prove2.me/theorems/a2d72483-dd51-44c6-8130-68498ed7091d
-- title:
--   Planar drawing existence passes to subgraphs
-- statement:
--   If a graph has a crossing-free drawing in the supplied sense, every subgraph on the same vertex type has one too. This preserves the exact vertex set and drawing witness, including injectivity and all arc intersection conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planarDrawingOn_mono__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G F : SimpleGraph V} (hGF : G ≤ F)
    (hF : WilliamsonShmoys.HasPlanarDrawingOn F) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
