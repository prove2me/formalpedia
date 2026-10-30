-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:26:40.58698+00:00
-- url     : https://prove2.me/theorems/773def43-51d0-4e88-9145-3374877c471c
-- title:
--   Simple planar graphs satisfy the edge upper bound
-- statement:
--   For a finite simple graph on at least three vertices, a crossing-free drawing implies the usual planar edge upper bound. This supplies the Euler and face-incidence argument for the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
