-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:39:53.719423+00:00
-- url     : https://prove2.me/theorems/583f27ad-47a4-47de-b736-b8d370f6dd4f
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most `3|V|−6` edges. This is the Euler planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
