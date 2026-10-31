-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:39.226174+00:00
-- url     : https://prove2.me/theorems/27b8a194-6c54-4ca3-a684-9503cbbde751
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under edge inclusion among drawable graphs on the same vertex type has exactly 3|V| − 6 edges. Maximality forces a connected triangulation; Euler’s formula and face-edge incidence counting yield the stated count, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
