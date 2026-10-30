-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:13:01.083094+00:00
-- url     : https://prove2.me/theorems/92968d93-3ce8-4b3b-823b-5613f2821c0d
-- title:
--   Euler upper bound for a planar simple graph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
