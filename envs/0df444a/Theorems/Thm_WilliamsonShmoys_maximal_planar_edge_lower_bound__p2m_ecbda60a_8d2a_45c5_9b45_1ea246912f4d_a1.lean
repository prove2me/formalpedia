-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:26.699911+00:00
-- url     : https://prove2.me/theorems/eaad4d3a-377c-4957-ad25-b7b8620e6c8f
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   Maximality among drawable supergraphs on the same vertex set forces at least 3n − 6 edges, expressed as 3n ≤ m + 6. A proof route is to extend the drawing to a triangulation on the same vertex set, apply maximality to identify that extension with L, and count the triangulation's edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
