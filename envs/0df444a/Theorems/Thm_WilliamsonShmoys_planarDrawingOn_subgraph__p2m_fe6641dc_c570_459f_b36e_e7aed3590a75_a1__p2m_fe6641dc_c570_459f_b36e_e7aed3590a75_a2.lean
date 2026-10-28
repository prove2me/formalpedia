-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:32:16.870233+00:00
-- url     : https://prove2.me/theorems/f20bba3a-3a22-4433-a179-e9264e99a9ad
-- title:
--   Restrict a planar drawing to a subgraph
-- statement:
--   If a graph's edges are a subset of another graph's edges, a drawing witness for the larger graph is also a drawing witness for the smaller graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
