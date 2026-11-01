-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:11.465729+00:00
-- url     : https://prove2.me/theorems/a2d35d35-9ed8-4ba3-917d-fe0f629ebdbd
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
