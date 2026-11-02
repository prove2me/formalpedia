-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:17.737939+00:00
-- url     : https://prove2.me/theorems/701795bb-5022-4e86-97bf-b07b90c6661c
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every graph with at least three vertices and a crossing-free drawing on those vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 ≤ Fintype.card V)
    [DecidableRel P.Adj] :
    P.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
