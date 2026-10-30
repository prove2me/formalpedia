-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:47.199997+00:00
-- url     : https://prove2.me/theorems/082382e5-3572-4220-9e97-f9d8fc451c82
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
