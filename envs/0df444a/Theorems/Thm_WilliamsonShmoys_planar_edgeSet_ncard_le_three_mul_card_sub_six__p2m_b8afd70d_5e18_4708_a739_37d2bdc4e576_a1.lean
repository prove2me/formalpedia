-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
-- name    : WilliamsonShmoys.planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:39:16.402675+00:00
-- url     : https://prove2.me/theorems/565cc4a2-872e-44c4-99ed-ae89e545f6b5
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. Prove by Euler’s formula and face-boundary counting, treating connected components as needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
