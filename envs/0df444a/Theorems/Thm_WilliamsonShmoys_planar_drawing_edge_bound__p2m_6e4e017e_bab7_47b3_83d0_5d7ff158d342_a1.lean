-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_6e4e017e_bab7_47b3_83d0_5d7ff158d342_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_6e4e017e_bab7_47b3_83d0_5d7ff158d342_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:00.135719+00:00
-- url     : https://prove2.me/theorems/f056e003-e39a-458f-bae2-0d8d8e18fd6e
-- title:
--   Sharp edge bound for a finite graph with a crossing-free drawing
-- statement:
--   For a finite simple graph with a crossing-free drawing, the edge count is at most 3n−6 for at least three vertices, at most one for two vertices, and zero for fewer than two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_6e4e017e_bab7_47b3_83d0_5d7ff158d342_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    if 3 ≤ Fintype.card V then
      G.edgeSet.ncard ≤ 3 * Fintype.card V - 6
    else if 2 ≤ Fintype.card V then
      G.edgeSet.ncard ≤ 1
    else
      G.edgeSet.ncard = 0 := by sorry
