-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:11.105217+00:00
-- url     : https://prove2.me/theorems/dafc9680-9370-4a7d-835c-8ab6494e7297
-- title:
--   Planar edge count upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges. The strict lower bound on the vertex count covers the n=3 boundary and avoids applying the Euler edge inequality outside its range.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
