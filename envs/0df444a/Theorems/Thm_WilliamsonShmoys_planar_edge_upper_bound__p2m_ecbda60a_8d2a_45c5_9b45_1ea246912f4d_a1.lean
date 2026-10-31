-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:33.721657+00:00
-- url     : https://prove2.me/theorems/7ae41427-8c04-422e-92b9-bd045ddeec30
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3n − 6 edges, expressed without truncated subtraction as m + 6 ≤ 3n.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
