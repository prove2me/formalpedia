-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:38.777772+00:00
-- url     : https://prove2.me/theorems/9d0fb3ab-d66a-4954-897e-7905864f2bd9
-- title:
--   Euler upper bound for a simple planar graph
-- statement:
--   For a finite simple graph with a crossing-free drawing and at least three vertices, the number of edges is at most 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
