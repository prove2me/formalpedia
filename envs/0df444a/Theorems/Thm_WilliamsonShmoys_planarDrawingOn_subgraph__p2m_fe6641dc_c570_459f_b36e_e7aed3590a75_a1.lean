-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:59:56.435909+00:00
-- url     : https://prove2.me/theorems/c5a4b3c1-a685-41d4-a7b9-61859469e7d6
-- title:
--   Restrict a planar drawing to a subgraph
-- statement:
--   If one graph's edges are a subset of another's, any crossing-free drawing witness for the larger graph is also a drawing witness for the smaller graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
