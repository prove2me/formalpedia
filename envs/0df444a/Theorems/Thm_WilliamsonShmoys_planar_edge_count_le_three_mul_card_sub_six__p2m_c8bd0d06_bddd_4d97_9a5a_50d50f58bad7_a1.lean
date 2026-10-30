-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_le_three_mul_card_sub_six__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- name    : WilliamsonShmoys.planar_edge_count_le_three_mul_card_sub_six__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:08.885982+00:00
-- url     : https://prove2.me/theorems/2911e589-9855-41f2-81aa-874f2d2a0dd0
-- title:
--   Euler bound for planar graph edges
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_le_three_mul_card_sub_six__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
