-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_upper_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_upper_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:42.817527+00:00
-- url     : https://prove2.me/theorems/18404f9f-9ab8-47a7-a1ab-ce02769fbc56
-- title:
--   Planar edge-count upper bound
-- statement:
--   Any graph with the specified crossing-free drawing on at least three vertices has at most 3n−6 edges. This is the ordinary simple planar graph upper bound, obtained from Euler’s formula and the fact that every face boundary has length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count_upper_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hV : 3 ≤ Fintype.card V) : Q.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
