-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
-- name    : WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:19.658919+00:00
-- url     : https://prove2.me/theorems/f665013f-6016-4c73-b421-fe3c911da6bd
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : LE.le 3 (Fintype.card V)) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
