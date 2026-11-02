-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:00:39.381805+00:00
-- url     : https://prove2.me/theorems/e5b59366-b679-40bb-b69e-6a506fdbf80c
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times its vertex count minus six edges. This includes disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
