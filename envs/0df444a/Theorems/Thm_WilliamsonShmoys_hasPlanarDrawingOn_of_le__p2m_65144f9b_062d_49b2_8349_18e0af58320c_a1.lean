-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_le__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_of_le__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:28.767352+00:00
-- url     : https://prove2.me/theorems/0d498d99-5ceb-4811-a8a1-413e1ce3fe1b
-- title:
--   Planar drawing restricts to subgraphs
-- statement:
--   Any subgraph of a graph with a crossing-free drawing has a crossing-free drawing, obtained by retaining the same vertex positions and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_of_le__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
