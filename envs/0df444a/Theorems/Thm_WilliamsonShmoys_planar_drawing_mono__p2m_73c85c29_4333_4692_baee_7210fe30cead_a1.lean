-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_mono__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
-- name    : WilliamsonShmoys.planar_drawing_mono__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:37:34.506643+00:00
-- url     : https://prove2.me/theorems/ef2a0659-6cef-461e-8075-d5a2f1e97ba3
-- title:
--   A subgraph of a drawable graph is drawable
-- statement:
--   If G is a subgraph of H and H has a planar drawing under the target's definition, then G has a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_drawing_mono__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
