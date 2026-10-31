-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:59.523684+00:00
-- url     : https://prove2.me/theorems/3060859a-0839-41c9-be06-b54269f75aee
-- title:
--   Maximality forces the triangulation edge lower bound
-- statement:
--   A finite simple graph with a crossing-free drawing that is maximal among drawable supergraphs on the same vertices, and has at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J) :
    3 * Fintype.card V ≤ J.edgeSet.ncard + 6 := by sorry
