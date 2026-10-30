-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T11:35:00.931001+00:00
-- url     : https://prove2.me/theorems/2a72d934-5721-47e6-9f14-7bb2bf8ff8c2
-- title:
--   Simple planar graphs satisfy the extremal edge bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. The vertex-count hypothesis includes the smallest allowed case, |V| = 3; disconnected drawings are covered by the planar edge bound as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
