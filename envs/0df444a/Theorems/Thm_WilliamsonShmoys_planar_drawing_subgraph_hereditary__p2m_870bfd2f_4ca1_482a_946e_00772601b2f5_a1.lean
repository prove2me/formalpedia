-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph_hereditary__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph_hereditary__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:16.990996+00:00
-- url     : https://prove2.me/theorems/840ce3bb-4259-4b45-8a12-6394b31eacab
-- title:
--   Planar drawing is preserved by taking subgraphs
-- statement:
--   If H is a subgraph of a graph with a crossing-free drawing, H has a crossing-free drawing. Reuse the drawing witnesses for G and observe that every edge condition required for H is among the conditions already satisfied for G. This handles edge deletion without changing vertex locations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph_hereditary__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hHG : H ≤ G)
    (hDraw : HasPlanarDrawingOn G) :
    HasPlanarDrawingOn H := by
  sorry
